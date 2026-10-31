module

public import BusyBeaver.Counter

/-!
# 2D Longitudinal Space-Time Calculus (`BusyBeaver.Longitudinal`)

Polymorphic 2D space-time boundary-trace calculus (`DH0`, `DH`, `toDHCfg`, `SideRL`, `SideLR`,
`SegRR`, `SegLL`, `SegRL`, `SegLR`, `SideRLs`, `SegLRs`, `SegRLs`, `SegLLs`, `SideRLsHalt`),
involutive left/right machine mirroring (`flipTM`, `flipCfg`), unary and binary counter tile
libraries (`UC1`, `UC2`, `UC3`, `BCR`, `BC`), parametric Shift-Overflow Binary Counter closure
(`SBC`), and reflective bounded-configuration tile checkers (`BoundedConfig`).

All declarations live in `namespace BusyBeaver.Longitudinal` with `@[scoped simp]` attributes so
that importing `BusyBeaver.Basic` never alters the default `simp` set of existing proofs; activate
them in a proof file with `open BusyBeaver.Longitudinal` (or `open Longitudinal`).
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.Longitudinal

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

-- ============================================================================
-- 1. Local Multi-Step & Half-Tape Helpers
-- ============================================================================

@[scoped simp] private lemma default_head : (default : ListBlank Γ).head = default := rfl

@[scoped simp] private lemma default_tail : (default : ListBlank Γ).tail = default := rfl

@[scoped simp] private lemma multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 0 = some c := rfl

@[scoped simp] private lemma multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 1 = step M c := rfl

private lemma multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

private lemma multiStep_succ' (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  induction n generalizing c with
  | zero =>
    rw [multiStep_one]
    rcases step M c with _ | c' <;> rfl
  | succ n ih =>
    rw [multiStep_succ, ih]
    rcases step M c with _ | c'
    · rfl
    · simp only [Option.bind_some, ← multiStep_succ]

private lemma multiStep_add (M : Machine Γ Λ) (c : Cfg Γ Λ) (m n : ℕ) :
    multiStep M c (m + n) = (multiStep M c m).bind (fun c' => multiStep M c' n) := by
  induction n with
  | zero => simp [multiStep_zero]
  | succ n ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    congr 1
    funext c'
    exact (multiStep_succ M c' n).symm

private lemma multiStep_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : ℕ}
    (h₁ : multiStep M c₁ m = some c₂) (h₂ : multiStep M c₂ n = some c₃) :
    multiStep M c₁ (m + n) = some c₃ := by
  rw [multiStep_add, h₁, Option.bind_some, h₂]

lemma stepStar_refl (M : Machine Γ Λ) (c : Cfg Γ Λ) : c [M]⊢* c :=
  ⟨0, rfl⟩

lemma stepStar_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢* c₃ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn⟩
  exact ⟨m + n, multiStep_trans hm hn⟩

lemma stepPlus_to_stepStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢⁺ c₂) : c₁ [M]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩
  exact ⟨n, hn⟩

lemma stepPlus_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨m, hm_pos, hm⟩
  rcases h₂ with ⟨n, _, hn⟩
  exact ⟨m + n, Nat.add_pos_left hm_pos n, multiStep_trans hm hn⟩

lemma stepPlus_stepStar_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨m, hm_pos, hm⟩
  rcases h₂ with ⟨n, hn⟩
  exact ⟨m + n, Nat.add_pos_left hm_pos n, multiStep_trans hm hn⟩

lemma stepStar_stepPlus_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn_pos, hn⟩
  exact ⟨m + n, Nat.add_pos_right m hn_pos, multiStep_trans hm hn⟩

@[scoped simp] lemma append_nil (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl

@[scoped simp] lemma append_cons (a : Γ) (w : List Γ) (s : ListBlank Γ) :
    (a :: w) +> s = a >> (w +> s) := rfl

@[scoped simp] lemma append_assoc (w₁ w₂ : List Γ) (s : ListBlank Γ) :
    (w₁ ++ w₂) +> s = w₁ +> (w₂ +> s) := by
  induction w₁ with
  | nil => rfl
  | cons a w₁ ih => simp only [List.cons_append, append_cons, ih]

omit [Inhabited Γ] [Inhabited Λ] in
@[scoped simp] lemma pow_zero_list {α : Type*} (l : List α) : l ^ (0 : ℕ) = [] := rfl

omit [Inhabited Γ] [Inhabited Λ] in
@[scoped simp] lemma pow_succ_list {α : Type*} (l : List α) (n : ℕ) :
    l ^ (n + 1) = l ++ l ^ n := rfl

omit [Inhabited Γ] [Inhabited Λ] in
lemma pow_one_list {α : Type*} (l : List α) : l ^ (1 : ℕ) = l := by
  change l ++ [] = l
  exact List.append_nil l

omit [Inhabited Γ] [Inhabited Λ] in
lemma pow_add_list {α : Type*} (l : List α) (m n : ℕ) :
    l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [pow_zero_list]
  | succ m ih => rw [Nat.succ_add, pow_succ_list, pow_succ_list, ih, List.append_assoc]

omit [Inhabited Γ] [Inhabited Λ] in
lemma pow_succ_list' {α : Type*} (l : List α) (n : ℕ) :
    l ^ (n + 1) = l ^ n ++ l := by
  rw [pow_add_list, pow_one_list]

omit [Inhabited Γ] [Inhabited Λ] in
lemma pow_mul_list {α : Type*} (l : List α) (m n : ℕ) :
    l ^ (m * n) = (l ^ m) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, pow_add_list, ih, pow_succ_list']

-- ============================================================================
-- 2. Involutive Machine & Configuration Mirroring (`flipTM`, `flipCfg`)
-- ============================================================================

/-- Swap left and right tape directions. -/
def flipDir : Dir → Dir
  | .left => .right
  | .right => .left

/-- Mirror a statement's movement direction. -/
def flipStmt (s : Stmt Γ) : Stmt Γ :=
  ⟨s.symbol, flipDir s.dir⟩

/-- Mirror a Turing machine by flipping all transition directions (`flip tm` in `busycoq`). -/
def flipTM (M : Machine Γ Λ) : Machine Γ Λ :=
  fun q a => (M q a).map (fun (q', s) => (q', flipStmt s))

/-- Mirror a tape by exchanging its left and right half-tapes. -/
def flipTape (T : Tape Γ) : Tape Γ :=
  ⟨T.head, T.right, T.left⟩

/-- Mirror a configuration by exchanging its left and right half-tapes. -/
def flipCfg (c : Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨c.q, flipTape c.tape⟩

@[scoped simp] theorem flipDir_flipDir (d : Dir) : flipDir (flipDir d) = d := by
  cases d <;> rfl

@[scoped simp] theorem flipStmt_flipStmt (s : Stmt Γ) : flipStmt (flipStmt s) = s := by
  rcases s with ⟨a, d⟩
  simp [flipStmt]

@[scoped simp] theorem flipTM_flipTM (M : Machine Γ Λ) : flipTM (flipTM M) = M := by
  funext q a
  simp only [flipTM, Option.map_map]
  rcases M q a with _ | ⟨q', s⟩
  · rfl
  · simp [Function.comp]

@[scoped simp] theorem flipTape_flipTape (T : Tape Γ) : flipTape (flipTape T) = T := by
  rcases T with ⟨h, l, r⟩
  rfl

@[scoped simp] theorem flipCfg_flipCfg (c : Cfg Γ Λ) : flipCfg (flipCfg c) = c := by
  rcases c with ⟨q, ⟨h, l, r⟩⟩
  rfl

@[scoped simp] theorem flipCfg_headRight (q : Λ) (l r : ListBlank Γ) :
    flipCfg (l {{q}}> r) = r <{{q}} l :=
  rfl

@[scoped simp] theorem flipCfg_headLeft (q : Λ) (l r : ListBlank Γ) :
    flipCfg (l <{{q}} r) = r {{q}}> l :=
  rfl

theorem step_flipTM (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    step (flipTM M) (flipCfg c) = (step M c).map flipCfg := by
  rcases c with ⟨_ | q, ⟨h, l, r⟩⟩
  · rfl
  · simp only [flipCfg, flipTape, step, flipTM]
    rcases M q h with _ | ⟨q', ⟨a, _ | _⟩⟩ <;> rfl

theorem multiStep_flipTM (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep (flipTM M) (flipCfg c) n = (multiStep M c n).map flipCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ, multiStep_succ, ih]
    rcases multiStep M c n with _ | c'
    · rfl
    · exact step_flipTM M c'

theorem step_flipTM_of_step {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢ c₂) : (flipCfg c₁) [flipTM M]⊢ (flipCfg c₂) := by
  rw [step_flipTM, h]
  rfl

theorem stepStar_flipTM {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢* c₂) : (flipCfg c₁) [flipTM M]⊢* (flipCfg c₂) := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [multiStep_flipTM, hn]
  rfl

theorem stepPlus_flipTM {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢⁺ c₂) : (flipCfg c₁) [flipTM M]⊢⁺ (flipCfg c₂) := by
  rcases h with ⟨n, hn_pos, hn⟩
  refine ⟨n, hn_pos, ?_⟩
  rw [multiStep_flipTM, hn]
  rfl

theorem stepStar_unflipTM {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : (flipCfg c₁) [flipTM M]⊢* (flipCfg c₂)) : c₁ [M]⊢* c₂ := by
  simpa using stepStar_flipTM h

theorem stepPlus_unflipTM {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : (flipCfg c₁) [flipTM M]⊢⁺ (flipCfg c₂)) : c₁ [M]⊢⁺ c₂ := by
  simpa using stepPlus_flipTM h

-- ============================================================================
-- 3. Directed-Head Words (`DH0`, `DH`, `toDHCfg`) & 1-Transition Primitives
-- ============================================================================

/-- Directed-head boundary state: control state paired with a local tape word. -/
abbrev DH0 (Γ Λ : Type*) := Λ × List Γ

/-- Oriented directed-head boundary state: `DH0` paired with a movement direction. -/
abbrev DH (Γ Λ : Type*) := DH0 Γ Λ × Dir

/-- Realize an oriented directed-head state `(h, d)` between half-tapes `l` and `r`. -/
def toDHCfg (x : DH Γ Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  match x with
  | ((q, s), .right) => (s +> l) {{q}}> r
  | ((q, s), .left) => l <{{q}} (s +> r)

@[scoped simp] theorem toDHCfg_right (q : Λ) (s : List Γ) (l r : ListBlank Γ) :
    toDHCfg ((q, s), .right) l r = (s +> l) {{q}}> r := rfl

@[scoped simp] theorem toDHCfg_left (q : Λ) (s : List Γ) (l r : ListBlank Γ) :
    toDHCfg ((q, s), .left) l r = l <{{q}} (s +> r) := rfl

@[scoped simp] theorem flipCfg_toDHCfg (h : DH0 Γ Λ) (d : Dir) (l r : ListBlank Γ) :
    flipCfg (toDHCfg (h, d) l r) = toDHCfg (h, flipDir d) r l := by
  rcases h with ⟨q, s⟩
  cases d <;> rfl

theorem toDHCfg_stepPlus_flip {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {d₁ d₂ : Dir}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (h : (toDHCfg (h₁, d₁) l₁ r₁) [M]⊢⁺ (toDHCfg (h₂, d₂) l₂ r₂)) :
    (toDHCfg (h₁, flipDir d₁) r₁ l₁) [flipTM M]⊢⁺ (toDHCfg (h₂, flipDir d₂) r₂ l₂) := by
  have h' := stepPlus_flipTM h
  rwa [flipCfg_toDHCfg, flipCfg_toDHCfg] at h'

theorem toDHCfg_stepPlus_unflip {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {d₁ d₂ : Dir}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (h : (toDHCfg (h₁, d₁) l₁ r₁) [flipTM M]⊢⁺ (toDHCfg (h₂, d₂) l₂ r₂)) :
    (toDHCfg (h₁, flipDir d₁) r₁ l₁) [M]⊢⁺ (toDHCfg (h₂, flipDir d₂) r₂ l₂) := by
  have h' := toDHCfg_stepPlus_flip h
  rwa [flipTM_flipTM] at h'

theorem toDHCfg_stepStar_flip {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {d₁ d₂ : Dir}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (h : (toDHCfg (h₁, d₁) l₁ r₁) [M]⊢* (toDHCfg (h₂, d₂) l₂ r₂)) :
    (toDHCfg (h₁, flipDir d₁) r₁ l₁) [flipTM M]⊢* (toDHCfg (h₂, flipDir d₂) r₂ l₂) := by
  have h' := stepStar_flipTM h
  rwa [flipCfg_toDHCfg, flipCfg_toDHCfg] at h'

theorem toDHCfg_stepStar_unflip {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {d₁ d₂ : Dir}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (h : (toDHCfg (h₁, d₁) l₁ r₁) [flipTM M]⊢* (toDHCfg (h₂, d₂) l₂ r₂)) :
    (toDHCfg (h₁, flipDir d₁) r₁ l₁) [M]⊢* (toDHCfg (h₂, flipDir d₂) r₂ l₂) := by
  have h' := toDHCfg_stepStar_flip h
  rwa [flipTM_flipTM] at h'

/-- Right-half-tape reflection (`sideRL` in `busycoq`): enters `r₁` moving right in `h₁` and exits
left in `h₂` leaving `r₂`, uniformly in the left half-tape `l`. -/
def SideRL (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (r₁ r₂ : ListBlank Γ) : Prop :=
  ∀ l, (toDHCfg (h₁, .right) l r₁) [M]⊢⁺ (toDHCfg (h₂, .left) l r₂)

/-- Left-half-tape reflection (`sideLR` in `busycoq`): enters `l₁` moving left in `h₁` and exits
right in `h₂` leaving `l₂`, uniformly in the right half-tape `r`. -/
def SideLR (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (l₁ l₂ : ListBlank Γ) : Prop :=
  ∀ r, (toDHCfg (h₁, .left) l₁ r) [M]⊢⁺ (toDHCfg (h₂, .right) l₂ r)

/-- Rightward finite-segment traversal (`segRR` in `busycoq`). -/
def SegRR (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (w₁ w₂ : List Γ) : Prop :=
  ∀ l r, (toDHCfg (h₁, .right) l (w₁ +> r)) [M]⊢* (toDHCfg (h₂, .right) (w₂ +> l) r)

/-- Leftward finite-segment traversal (`segLL` in `busycoq`). -/
def SegLL (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (w₁ w₂ : List Γ) : Prop :=
  ∀ l r, (toDHCfg (h₁, .left) (w₁ +> l) r) [M]⊢* (toDHCfg (h₂, .left) l (w₂ +> r))

/-- Right-to-left finite-segment reflection (`segRL` in `busycoq`). -/
def SegRL (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (w₁ w₂ : List Γ) : Prop :=
  ∀ l r, (toDHCfg (h₁, .right) l (w₁ +> r)) [M]⊢⁺ (toDHCfg (h₂, .left) l (w₂ +> r))

/-- Left-to-right finite-segment reflection (`segLR` in `busycoq`). -/
def SegLR (M : Machine Γ Λ) (h₁ h₂ : DH0 Γ Λ) (w₁ w₂ : List Γ) : Prop :=
  ∀ l r, (toDHCfg (h₁, .left) (w₁ +> l) r) [M]⊢* (toDHCfg (h₂, .right) (w₂ +> l) r)

-- ============================================================================
-- 4. Boundary Signal Lists (`lrcons`, `lcons`, `rcons`) & 2D Tile Relations
-- ============================================================================

omit [Inhabited Γ] [Inhabited Λ] in
/-- Interleave a starting right-entry signal `l`, a list of left-to-right bounce pairs `ls`, and a
final left-exit signal `r` into a right-boundary `(entry, exit)` list. -/
def lrcons {α : Type*} (l : α) : List (α × α) → α → List (α × α)
  | [], r => [(l, r)]
  | (a, b) :: t, r => (l, a) :: lrcons b t r

omit [Inhabited Γ] [Inhabited Λ] in
/-- Pair an initial signal `l` with a list of opposite-side bounce pairs `ls`, returning the
paired signal list and the final exit signal. -/
def lcons {α : Type*} (l : α) : List (α × α) → List (α × α) × α
  | [] => ([], l)
  | (a, b) :: t =>
    let (x, y) := lcons b t
    ((l, a) :: x, y)

omit [Inhabited Γ] [Inhabited Λ] in
/-- Split the head signal off `ls` paired with trailing signal `r`. -/
def rcons {α : Type*} : List (α × α) → α → α × List (α × α)
  | [], r => (r, [])
  | (a, b) :: t, r => (a, lrcons b t r)

omit [Inhabited Γ] [Inhabited Λ] in
theorem lrcons_lrcons {α : Type*} (h₁ h₂ : α) (ls : List (α × α)) (h₃ h₄ : α) :
    lrcons h₁ (lrcons h₂ ls h₃) h₄ = (h₁, h₂) :: ls ++ [(h₃, h₄)] := by
  induction ls generalizing h₁ h₂ h₃ h₄ with
  | nil => rfl
  | cons ab t ih =>
    rcases ab with ⟨a, b⟩
    simp only [lrcons, List.cons_append, ih]

omit [Inhabited Γ] [Inhabited Λ] in
theorem lrcons_app {α : Type*} (h₁ : α) (ls₀ : List (α × α)) (h₂ h₀ : α)
    (ls₁ : List (α × α)) (h₃ : α) :
    lrcons h₁ ls₀ h₂ ++ lrcons h₀ ls₁ h₃ = lrcons h₁ (ls₀ ++ (h₂, h₀) :: ls₁) h₃ := by
  induction ls₀ generalizing h₁ with
  | nil => rfl
  | cons ab t ih =>
    rcases ab with ⟨a, b⟩
    simp only [lrcons, List.cons_append, ih]

omit [Inhabited Γ] [Inhabited Λ] in
theorem lrcons_same {α : Type*} (h₁ h₂ : α) (n : ℕ) :
    lrcons h₁ ([(h₂, h₁)] ^ n) h₂ = [(h₁, h₂)] ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (h₁, h₂) :: lrcons h₁ ([(h₂, h₁)] ^ n) h₂ = (h₁, h₂) :: ([(h₁, h₂)] ^ (n + 1))
    rw [ih]

omit [Inhabited Γ] [Inhabited Λ] in
theorem lrcons_lpow1 {α : Type*} (h₁ h₂ : α) {n : ℕ} (hn : n ≠ 0) :
    lrcons h₁ ([(h₂, h₁)] ^ (n - 1)) h₂ = [(h₁, h₂)] ^ n := by
  rcases n with _ | n
  · exact absurd rfl hn
  · exact lrcons_same h₁ h₂ n

/-- Multi-visit right half-tape reflection (`sideRLs` in `busycoq`). -/
inductive SideRLs (M : Machine Γ Λ) :
    List (DH0 Γ Λ × DH0 Γ Λ) → ListBlank Γ → ListBlank Γ → Prop where
  | nil (r : ListBlank Γ) : SideRLs M [] r r
  | cons {h₁ h₂ : DH0 Γ Λ} {hs : List (DH0 Γ Λ × DH0 Γ Λ)} {r₁ r₂ r₃ : ListBlank Γ} :
      SideRL M h₁ h₂ r₁ r₂ → SideRLs M hs r₂ r₃ → SideRLs M ((h₁, h₂) :: hs) r₁ r₃

/-- Multi-visit left-to-right segment reflection (`segLRs` in `busycoq`). -/
inductive SegLRs (M : Machine Γ Λ) :
    List (DH0 Γ Λ × DH0 Γ Λ) → List Γ → List Γ → Prop where
  | nil (w : List Γ) : SegLRs M [] w w
  | cons {h₁ h₂ : DH0 Γ Λ} {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ w₃ : List Γ} :
      SegLR M h₁ h₂ w₁ w₂ → SegLRs M ls w₂ w₃ → SegLRs M ((h₁, h₂) :: ls) w₁ w₃

/-- 2D longitudinal space-time tile relation (`segRLs` in `busycoq`): transforms a left-boundary
signal sequence `ls₁` into a right-boundary signal sequence `ls₂` while evolving the finite tape
segment from `w₁` to `w₂`. -/
inductive SegRLs (M : Machine Γ Λ) :
    List (DH0 Γ Λ × DH0 Γ Λ) → List (DH0 Γ Λ × DH0 Γ Λ) → List Γ → List Γ → Prop where
  | nil (w : List Γ) : SegRLs M [] [] w w
  | cons {h₁ h₂ : DH0 Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ w₃ : List Γ} :
      SegRL M h₁ h₂ w₁ w₂ →
      SegRLs M ls₁ ls₂ w₂ w₃ →
      SegRLs M ((h₁, h₂) :: ls₁) ls₂ w₁ w₃
  | lrcons {h₁ h₂ h₃ h₄ : DH0 Γ Λ} {ls₂ ls₃ ls₄ : List (DH0 Γ Λ × DH0 Γ Λ)}
      {w₁ w₂ w₃ w₄ w₅ : List Γ} :
      SegRR M h₁ h₃ w₁ w₃ →
      SegLL M h₄ h₂ w₄ w₅ →
      SegLRs M ls₂ w₃ w₄ →
      SegRLs M ls₃ ls₄ w₅ w₂ →
      SegRLs M ((h₁, h₂) :: ls₃) (lrcons h₃ ls₂ h₄ ++ ls₄) w₁ w₂

/-- Auxiliary left-exit longitudinal tile relation (`segLLs` in `busycoq`) used by the reflective
tile verifier. -/
inductive SegLLs (M : Machine Γ Λ) :
    DH0 Γ Λ → List (DH0 Γ Λ × DH0 Γ Λ) → DH0 Γ Λ → List (DH0 Γ Λ × DH0 Γ Λ) →
      List Γ → List Γ → Prop where
  | intro {ls₂ ls₃ ls₄ ls₂' : List (DH0 Γ Λ × DH0 Γ Λ)} {w₂ w₃ w₄ w₅ : List Γ}
      {h₂ h₄ h₄' : DH0 Γ Λ} :
      SegLRs M ls₂ w₃ w₄ →
      SegLL M h₄ h₂ w₄ w₅ →
      SegRLs M ls₃ ls₄ w₅ w₂ →
      rcons ls₂ h₄ = (h₄', ls₂') →
      SegLLs M h₂ ls₃ h₄' (ls₂' ++ ls₄) w₃ w₂

-- ============================================================================
-- 5. Horizontal & Vertical Composition, Splitting & Wall Laws
-- ============================================================================

theorem SideRLs.single {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {r₁ r₂ : ListBlank Γ}
    (h : SideRL M h₁ h₂ r₁ r₂) : SideRLs M [(h₁, h₂)] r₁ r₂ :=
  .cons h (.nil r₂)

theorem SideRLs.elim_single {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {r r' : ListBlank Γ}
    (h : SideRLs M [(hR, hL)] r r') (l : ListBlank Γ) :
    (toDHCfg (hR, .right) l r) [M]⊢⁺ (toDHCfg (hL, .left) l r') := by
  cases h with
  | cons h₁ h₂ =>
    cases h₂
    exact h₁ l

theorem SideRLs.elim_single_left {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {l l' : ListBlank Γ}
    (h : SideRLs (flipTM M) [(hL, hR)] l l') (r : ListBlank Γ) :
    (toDHCfg (hL, .left) l r) [M]⊢⁺ (toDHCfg (hR, .right) l' r) :=
  toDHCfg_stepPlus_unflip (h.elim_single r)

theorem SideRLs.trans {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r₁ r₂ r₃ : ListBlank Γ}
    (h₁ : SideRLs M ls₁ r₁ r₂) (h₂ : SideRLs M ls₂ r₂ r₃) :
    SideRLs M (ls₁ ++ ls₂) r₁ r₃ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

theorem SideRLs.split {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r₁ r₂ : ListBlank Γ}
    (h : SideRLs M (ls₁ ++ ls₂) r₁ r₂) :
    ∃ r₃, SideRLs M ls₁ r₁ r₃ ∧ SideRLs M ls₂ r₃ r₂ := by
  induction ls₁ generalizing r₁ with
  | nil => exact ⟨r₁, .nil r₁, h⟩
  | cons ab ls₁ ih =>
    cases h with
    | cons h_first h_rest =>
      obtain ⟨r₃, h₁, h₂⟩ := ih h_rest
      exact ⟨r₃, .cons h_first h₁, h₂⟩

theorem SideRLs.trans_add {M : Machine Γ Λ} {h : List (DH0 Γ Λ × DH0 Γ Λ)} {n₁ n₂ : ℕ}
    {r₁ r₂ r₃ : ListBlank Γ}
    (h₁ : SideRLs M (h ^ n₁) r₁ r₃) (h₂ : SideRLs M (h ^ n₂) r₃ r₂) :
    SideRLs M (h ^ (n₁ + n₂)) r₁ r₂ := by
  rw [pow_add_list]
  exact h₁.trans h₂

theorem SideRLs.trans_succ {M : Machine Γ Λ} {h : List (DH0 Γ Λ × DH0 Γ Λ)} {n : ℕ}
    {r₁ r₂ r₃ : ListBlank Γ}
    (h₁ : SideRLs M (h ^ n) r₁ r₃) (h₂ : SideRLs M h r₃ r₂) :
    SideRLs M (h ^ (n + 1)) r₁ r₂ := by
  rw [ ← pow_one_list h] at h₂
  exact h₁.trans_add h₂

theorem SideRLs.wall {M : Machine Γ Λ} {h : List (DH0 Γ Λ × DH0 Γ Λ)} {r : ListBlank Γ}
    (hw : SideRLs M h r r) (k : ℕ) :
    SideRLs M (h ^ k) r r := by
  induction k with
  | zero => exact .nil r
  | succ k ih => exact hw.trans ih

theorem SegLRs.app {M : Machine Γ Λ} {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ : List Γ}
    (h : SegLRs M ls w₁ w₂) (w₃ : List Γ) :
    SegLRs M ls (w₁ ++ w₃) (w₂ ++ w₃) := by
  induction h with
  | nil _ => exact .nil _
  | cons h_lr _ ih =>
    refine .cons (fun l r => ?_) ih
    rw [append_assoc, append_assoc]
    exact h_lr (w₃ +> l) r

theorem SegLRs.trans {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ : List Γ}
    (h₁ : SegLRs M ls₁ w₁ w₂) (h₂ : SegLRs M ls₂ w₂ w₃) :
    SegLRs M (ls₁ ++ ls₂) w₁ w₃ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons h_lr _ ih => exact .cons h_lr (ih h₂)

theorem SegRLs.trans {M : Machine Γ Λ} {ls₁ ls₂ ls₃ ls₄ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ : List Γ}
    (h₁ : SegRLs M ls₁ ls₂ w₁ w₂) (h₂ : SegRLs M ls₃ ls₄ w₂ w₃) :
    SegRLs M (ls₁ ++ ls₃) (ls₂ ++ ls₄) w₁ w₃ := by
  induction h₁ generalizing ls₃ ls₄ w₃ with
  | nil _ => exact h₂
  | cons h_rl _ ih => exact .cons h_rl (ih h₂)
  | lrcons h_rr h_ll h_lrs _ ih =>
    rw [List.append_assoc]
    exact .lrcons h_rr h_ll h_lrs (ih h₂)

theorem SegRLs.split {M : Machine Γ Λ} {ls₁ ls₂ ls₃ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ : List Γ}
    (h : SegRLs M (ls₁ ++ ls₂) ls₃ w₁ w₂) :
    ∃ ls₄ ls₅ w₃,
      SegRLs M ls₁ ls₄ w₁ w₃ ∧
      SegRLs M ls₂ ls₅ w₃ w₂ ∧
      ls₃ = ls₄ ++ ls₅ := by
  induction ls₁ generalizing ls₃ w₁ with
  | nil => exact ⟨[], ls₃, w₁, .nil w₁, h, rfl⟩
  | cons ab ls₁ ih =>
    cases h with
    | cons h_rl h_rest =>
      obtain ⟨ls₄, ls₅, w₃, h₁, h₂, rfl⟩ := ih h_rest
      exact ⟨ls₄, ls₅, w₃, .cons h_rl h₁, h₂, rfl⟩
    | lrcons h_rr h_ll h_lrs h_rest =>
      obtain ⟨ls₄, ls₅, w₃, h₁, h₂, rfl⟩ := ih h_rest
      exact ⟨Longitudinal.lrcons _ _ _ ++ ls₄, ls₅, w₃, .lrcons h_rr h_ll h_lrs h₁, h₂,
        by rw [List.append_assoc]⟩

private theorem segRLs_concat_aux' {M : Machine Γ Λ}
    {h₂ h₃ h₄ : DH0 Γ Λ} {w₂ w₃ w₄ w₅ w₆ : List Γ}
    {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    (hll : SegLL M h₄ h₂ w₄ w₂)
    (hlr : SegLRs M ls₁ w₃ w₄)
    (hrl : SegRLs M (lrcons h₃ ls₁ h₄) ls₂ w₅ w₆) :
    ((∀ l r, (toDHCfg (h₃, .right) (w₃ +> l) (w₅ +> r)) [M]⊢⁺
        (toDHCfg (h₂, .left) l (w₂ +> (w₆ +> r)))) ∧ ls₂ = []) ∨
    ∃ h₅ h₆ w₇ w₈ ls₂',
      (∀ l r, (toDHCfg (h₃, .right) (w₃ +> l) (w₅ +> r)) [M]⊢*
        (toDHCfg (h₅, .right) (w₇ +> l) r)) ∧
      SegLL M h₆ h₂ w₈ (w₂ ++ w₆) ∧
      SegLRs M ls₂' w₇ w₈ ∧
      ls₂ = lrcons h₅ ls₂' h₆ := by
  induction hlr generalizing h₃ w₅ w₆ ls₂ with
  | nil w₃ =>
    cases hrl with
    | cons h_rl h_tail =>
      cases h_tail
      refine Or.inl ⟨fun l r => ?_, rfl⟩
      exact stepPlus_stepStar_trans (h_rl (w₃ +> l) r) (hll l (w₆ +> r))
    | lrcons h_rr h_ll h_lrs h_tail =>
      cases h_tail
      refine Or.inr ⟨_, _, _ ++ w₃, _ ++ w₃, _, ?_, ?_, h_lrs.app w₃, List.append_nil _⟩
      · intro l r
        rw [append_assoc]
        exact h_rr (w₃ +> l) r
      · intro l r
        rw [append_assoc, append_assoc]
        exact stepStar_trans (h_ll (w₃ +> l) r) (hll l (w₆ +> r))
  | @cons a b ls₁ w₃ w_mid w₄ h_lr hlr_rest ih =>
    cases hrl with
    | cons h_rl hrl_rest =>
      rcases ih hll hrl_rest with ⟨h_step, rfl⟩ | ⟨h₅', h₆', w₇', w₈', ls₂', h_step, h_ll', h_lrs', h_eq⟩
      · refine Or.inl ⟨fun l r => ?_, rfl⟩
        exact stepPlus_trans
          (stepPlus_stepStar_trans (h_rl (w₃ +> l) r) (h_lr l (_ +> r)))
          (h_step l r)
      · refine Or.inr ⟨h₅', h₆', w₇', w₈', ls₂', fun l r => ?_, h_ll', h_lrs', h_eq⟩
        exact stepStar_trans
          (stepPlus_to_stepStar (stepPlus_stepStar_trans (h_rl (w₃ +> l) r) (h_lr l (_ +> r))))
          (h_step l r)
    | lrcons h_rr h_ll h_lrs hrl_rest =>
      rcases ih hll hrl_rest with ⟨h_step, rfl⟩ | ⟨h₅', h₆', w₇', w₈', ls₂', h_step, h_ll', h_lrs', rfl⟩
      · refine Or.inr ⟨_, _, _ ++ w₃, _ ++ w₃, _, ?_, ?_, h_lrs.app w₃, List.append_nil _⟩
        · intro l r
          rw [append_assoc]
          exact h_rr (w₃ +> l) r
        · intro l r
          rw [append_assoc, append_assoc]
          exact stepStar_trans (h_ll (w₃ +> l) r)
            (stepStar_trans (h_lr l (_ +> r)) (stepPlus_to_stepStar (h_step l r)))
      · have h_lrs'' := (h_lrs.app w₃).trans (.cons (fun l r => by
          rw [append_assoc]
          exact stepStar_trans (h_ll (w₃ +> l) r)
            (stepStar_trans (h_lr l (_ +> r)) (h_step l r))) h_lrs')
        refine Or.inr ⟨_, h₆', _, w₈', _, ?_, h_ll', h_lrs'', lrcons_app _ _ _ _ _ _⟩
        intro l r
        rw [append_assoc]
        exact h_rr (w₃ +> l) r

private theorem segRLs_concat_aux {M : Machine Γ Λ}
    {h₁ h₂ h₃ h₄ : DH0 Γ Λ} {w₁ w₂ w₃ w₄ w₅ w₆ : List Γ}
    {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    (hrr : SegRR M h₁ h₃ w₁ w₃)
    (hll : SegLL M h₄ h₂ w₄ w₂)
    (hlr : SegLRs M ls₁ w₃ w₄)
    (hrl : SegRLs M (lrcons h₃ ls₁ h₄) ls₂ w₅ w₆) :
    (SegRL M h₁ h₂ (w₁ ++ w₅) (w₂ ++ w₆) ∧ ls₂ = []) ∨
    ∃ h₅ h₆ w₇ w₈ ls₂',
      SegRR M h₁ h₅ (w₁ ++ w₅) w₇ ∧
      SegLL M h₆ h₂ w₈ (w₂ ++ w₆) ∧
      SegLRs M ls₂' w₇ w₈ ∧
      ls₂ = lrcons h₅ ls₂' h₆ := by
  rcases segRLs_concat_aux' hll hlr hrl with ⟨h_step, rfl⟩ | ⟨h₅, h₆, w₇, w₈, ls₂', h_step, h_ll', h_lrs', h_eq⟩
  · refine Or.inl ⟨fun l r => ?_, rfl⟩
    rw [append_assoc, append_assoc]
    exact stepStar_stepPlus_trans (hrr l (w₅ +> r)) (h_step l r)
  · refine Or.inr ⟨h₅, h₆, w₇, w₈, ls₂', fun l r => ?_, h_ll', h_lrs', h_eq⟩
    rw [append_assoc]
    exact stepStar_trans (hrr l (w₅ +> r)) (h_step l r)

/-- Horizontal composition of two 2D longitudinal space-time tiles (`segRLs_concat` in `busycoq`). -/
theorem SegRLs.concat {M : Machine Γ Λ} {ls₁ ls₂ ls₃ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ w₄ : List Γ}
    (h₁ : SegRLs M ls₁ ls₂ w₁ w₂) (h₂ : SegRLs M ls₂ ls₃ w₃ w₄) :
    SegRLs M ls₁ ls₃ (w₁ ++ w₃) (w₂ ++ w₄) := by
  induction h₁ generalizing ls₃ w₃ w₄ with
  | nil _ =>
    cases h₂
    exact .nil _
  | cons h_rl _ ih =>
    refine .cons (fun l r => ?_) (ih h₂)
    rw [append_assoc, append_assoc]
    exact h_rl l (w₃ +> r)
  | lrcons h_rr h_ll h_lrs _ ih =>
    obtain ⟨ls₅, ls₆, w_mid, h₂_left, h₂_right, rfl⟩ := h₂.split
    have ih_res := ih h₂_right
    rcases segRLs_concat_aux h_rr h_ll h_lrs h₂_left with
      ⟨h_rl, rfl⟩ | ⟨h₅, h₆, w₇, w₈, ls₂', h_rr', h_ll', h_lrs', rfl⟩
    · exact .cons h_rl ih_res
    · exact .lrcons h_rr' h_ll' h_lrs' ih_res

/-- Combine a left-to-right segment bounce sequence `SegLRs` with a right half-tape reflection
sequence `SideRLs`. -/
theorem SideRLs.segLRs_concat {M : Machine Γ Λ} {ls : List (DH0 Γ Λ × DH0 Γ Λ)}
    {h₁ h₂ : DH0 Γ Λ} {w₁ w₂ : List Γ} {r₁ r₂ : ListBlank Γ}
    (h_seg : SegLRs M ls w₁ w₂)
    (h_side : SideRLs M (lrcons h₁ ls h₂) r₁ r₂)
    (l : ListBlank Γ) :
    (toDHCfg (h₁, .right) (w₁ +> l) r₁) [M]⊢⁺ (toDHCfg (h₂, .left) (w₂ +> l) r₂) := by
  induction h_seg generalizing h₁ h₂ r₁ r₂ with
  | nil w =>
    exact h_side.elim_single (w +> l)
  | cons h_lr _ ih =>
    cases h_side with
    | cons h_first h_rest =>
      exact stepPlus_trans
        (stepPlus_stepStar_trans (h_first (_ +> l)) (h_lr l _))
        (ih h_rest)

/-- Act on a right half-tape reflection `SideRLs M ls₂ r₁ r₂` by prepending a 2D longitudinal tile
`SegRLs M ls₁ ls₂ w₁ w₂` (`segRLs_sideRLs_concat` in `busycoq`). -/
theorem SegRLs.sideRLs_concat {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ : List Γ} {r₁ r₂ : ListBlank Γ}
    (h_seg : SegRLs M ls₁ ls₂ w₁ w₂)
    (h_side : SideRLs M ls₂ r₁ r₂) :
    SideRLs M ls₁ (w₁ +> r₁) (w₂ +> r₂) := by
  induction h_seg generalizing r₁ r₂ with
  | nil _ =>
    cases h_side
    exact .nil _
  | cons h_rl _ ih =>
    exact .cons (fun l => h_rl l r₁) (ih h_side)
  | lrcons h_rr h_ll h_lrs _ ih =>
    obtain ⟨r_mid, h_side_left, h_side_right⟩ := h_side.split
    refine .cons (fun l => ?_) (ih h_side_right)
    exact stepStar_stepPlus_trans (h_rr l r₁)
      (stepPlus_stepStar_trans (h_side_left.segLRs_concat h_lrs l) (h_ll l r_mid))

/-- Glue a mirrored left-half-tape reflection `SideRLs (flipTM M)` with a right-half-tape reflection
`SideRLs M` into a full-tape `⊢⁺` transition (`sideRLs_concat` in `busycoq`). -/
theorem SideRLs.concat {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ}
    {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hl : SideRLs (flipTM M) ls l₁ l₂)
    (hr : SideRLs M (lrcons h₁ ls h₂) r₁ r₂) :
    (toDHCfg (h₁, .right) l₁ r₁) [M]⊢⁺ (toDHCfg (h₂, .left) l₂ r₂) := by
  induction ls generalizing h₁ h₂ l₁ l₂ r₁ r₂ with
  | nil =>
    cases hl
    exact hr.elim_single l₁
  | cons ab ls ih =>
    rcases ab with ⟨a, b⟩
    cases hl with
    | cons hl_first hl_rest =>
      cases hr with
      | cons hr_first hr_rest =>
        exact stepPlus_trans (hr_first l₁)
          (stepPlus_trans (toDHCfg_stepPlus_unflip (hl_first _)) (ih hl_rest hr_rest))

/-- Left-entry dual of `SideRLs.concat` (`sideRLs_concat_L` in `busycoq`). -/
theorem SideRLs.concat_L {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ}
    {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hl : SideRLs (flipTM M) (lrcons h₁ ls h₂) l₁ l₂)
    (hr : SideRLs M ls r₁ r₂) :
    (toDHCfg (h₁, .left) l₁ r₁) [M]⊢⁺ (toDHCfg (h₂, .right) l₂ r₂) := by
  have hr' : SideRLs (flipTM (flipTM M)) ls r₁ r₂ := by rwa [flipTM_flipTM]
  exact toDHCfg_stepPlus_unflip (SideRLs.concat hr' hl)

/-- Variant of `SideRLs.concat` using `lcons` exiting to the right (`sideRLs_concat_v2` in `busycoq`). -/
theorem SideRLs.concat_v2 {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ}
    {ls ls' : List (DH0 Γ Λ × DH0 Γ Λ)} {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hlc : lcons h₁ ls = (ls', h₂))
    (hne : ls ≠ [])
    (hl : SideRLs (flipTM M) ls l₁ l₂)
    (hr : SideRLs M ls' r₁ r₂) :
    (toDHCfg (h₁, .right) l₁ r₁) [M]⊢⁺ (toDHCfg (h₂, .right) l₂ r₂) := by
  induction ls generalizing h₁ h₂ ls' l₁ l₂ r₁ r₂ with
  | nil => exact absurd rfl hne
  | cons ab ls ih =>
    rcases ab with ⟨a, b⟩
    dsimp [lcons] at hlc
    rcases h_lcons : lcons b ls with ⟨ls'₀, h₂'⟩
    rw [h_lcons] at hlc
    cases hlc
    cases hl with
    | cons hl_first hl_rest =>
      cases hr with
      | cons hr_first hr_rest =>
        rcases ls with _ | ⟨cd, ls_tail⟩
        · injection h_lcons with h_nil h_eq
          subst h_nil h_eq
          cases hl_rest
          cases hr_rest
          exact stepPlus_trans (hr_first l₁) (toDHCfg_stepPlus_unflip (hl_first _))
        · have h_rec := ih h_lcons (List.cons_ne_nil cd ls_tail) hl_rest hr_rest
          exact stepPlus_trans (hr_first l₁)
            (stepPlus_trans (toDHCfg_stepPlus_unflip (hl_first _)) h_rec)

/-- Left-entry dual of `SideRLs.concat_v2` (`sideRLs_concat_v2_L` in `busycoq`). -/
theorem SideRLs.concat_v2_L {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ}
    {ls ls' : List (DH0 Γ Λ × DH0 Γ Λ)} {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hlc : lcons h₁ ls = (ls', h₂))
    (hne : ls ≠ [])
    (hl : SideRLs (flipTM M) ls' l₁ l₂)
    (hr : SideRLs M ls r₁ r₂) :
    (toDHCfg (h₁, .left) l₁ r₁) [M]⊢⁺ (toDHCfg (h₂, .left) l₂ r₂) := by
  have hr' : SideRLs (flipTM (flipTM M)) ls r₁ r₂ := by rwa [flipTM_flipTM]
  exact toDHCfg_stepPlus_unflip (SideRLs.concat_v2 hlc hne hr' hl)

/-- Equal-count ping-pong glue (`sideRLs_concat_1` in `busycoq`). -/
theorem SideRLs.concat_1 {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {n : ℕ}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hr : SideRLs M ([(hR, hL)] ^ n) r₁ r₂)
    (hl : SideRLs (flipTM M) ([(hL, hR)] ^ n) l₁ l₂) :
    (toDHCfg (hR, .right) l₁ r₁) [M]⊢* (toDHCfg (hR, .right) l₂ r₂) := by
  rcases n with _ | n
  · cases hr
    cases hl
    exact stepStar_refl M _
  · rw [← lrcons_same hR hL n] at hr
    have h_split : [(hL, hR)] ^ (n + 1) = [(hL, hR)] ^ n ++ [(hL, hR)] := by
      rw [pow_add_list, pow_one_list]
    rw [h_split] at hl
    obtain ⟨l₃, hl₁, hl₂⟩ := hl.split
    exact stepStar_trans
      (stepPlus_to_stepStar (SideRLs.concat hl₁ hr))
      (stepPlus_to_stepStar (hl₂.elim_single_left r₂))

/-- Left-entry equal-count ping-pong glue (`sideRLs_concat_1L` in `busycoq`). -/
theorem SideRLs.concat_1L {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {n : ℕ}
    {l₁ l₂ r₁ r₂ : ListBlank Γ}
    (hr : SideRLs M ([(hR, hL)] ^ n) r₁ r₂)
    (hl : SideRLs (flipTM M) ([(hL, hR)] ^ n) l₁ l₂) :
    (toDHCfg (hL, .left) l₁ r₁) [M]⊢* (toDHCfg (hL, .left) l₂ r₂) := by
  have hr' : SideRLs (flipTM (flipTM M)) ([(hR, hL)] ^ n) r₁ r₂ := by rwa [flipTM_flipTM]
  exact toDHCfg_stepStar_unflip (SideRLs.concat_1 hl hr')

theorem SegRLs.empty (M : Machine Γ Λ) (ls : List (DH0 Γ Λ × DH0 Γ Λ)) :
    SegRLs M ls ls [] [] := by
  induction ls with
  | nil => exact .nil []
  | cons ab ls ih =>
    rcases ab with ⟨a, b⟩
    exact .lrcons (fun l r => stepStar_refl M _) (fun l r => stepStar_refl M _) (.nil []) ih

theorem SegRLs.S' {M : Machine Γ Λ} {h₁ h₂ h₃ h₄ : DH0 Γ Λ}
    {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ w₃ w₄ : List Γ}
    (h_rr : SegRR M h₁ h₃ w₁ w₂)
    (h_ll : SegLL M h₄ h₂ w₂ w₃)
    (h_rest : SegRLs M ls₁ ls₂ w₃ w₄) :
    SegRLs M ((h₁, h₂) :: ls₁) ((h₃, h₄) :: ls₂) w₁ w₄ :=
  .lrcons h_rr h_ll (.nil w₂) h_rest

theorem SegRLs.wall {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ} {w w' : List Γ}
    (h_rr : SegRR M h₁ h₁ w w') (h_ll : SegLL M h₂ h₂ w' w) (n : ℕ) :
    SegRLs M ([(h₁, h₂)] ^ n) ([(h₁, h₂)] ^ n) w w := by
  induction n with
  | zero => exact .nil w
  | succ n ih => exact .S' h_rr h_ll ih

theorem SegRLs.wall' {M : Machine Γ Λ} {h₁ h₂ h₁' h₂' : DH0 Γ Λ} {w w' : List Γ}
    (h_rr : SegRR M h₁ h₁' w w') (h_ll : SegLL M h₂' h₂ w' w) (n : ℕ) :
    SegRLs M ([(h₁, h₂)] ^ n) ([(h₁', h₂')] ^ n) w w := by
  induction n with
  | zero => exact .nil w
  | succ n ih => exact .S' h_rr h_ll ih

theorem SegRLs.wall_pow {M : Machine Γ Λ} {h₁ h₂ : List (DH0 Γ Λ × DH0 Γ Λ)} {w : List Γ}
    (hw : SegRLs M h₁ h₂ w w) (n : ℕ) :
    SegRLs M (h₁ ^ n) (h₂ ^ n) w w := by
  induction n with
  | zero => exact .nil w
  | succ n ih => exact hw.trans ih

theorem SegRLs.trans_add {M : Machine Γ Λ} {h h' : List (DH0 Γ Λ × DH0 Γ Λ)}
    {n₁ n₂ n₁' n₂' : ℕ} {w₁ w₂ w₃ : List Γ}
    (h₁ : SegRLs M (h ^ n₁) (h' ^ n₁') w₁ w₃)
    (h₂ : SegRLs M (h ^ n₂) (h' ^ n₂') w₃ w₂) :
    SegRLs M (h ^ (n₁ + n₂)) (h' ^ (n₁' + n₂')) w₁ w₂ := by
  rw [pow_add_list, pow_add_list]
  exact h₁.trans h₂

theorem SegRLs.addmul {M : Machine Γ Λ} {h : List (DH0 Γ Λ × DH0 Γ Λ)}
    {a x b c : ℕ} {w₁ w₂ : List Γ}
    (hb : SegRLs M (h ^ b) (h ^ c) w₁ w₂)
    (ha : SegRLs M (h ^ a) h w₂ w₂) :
    SegRLs M (h ^ (x * a + b)) (h ^ (x + c)) w₁ w₂ := by
  rw [Nat.add_comm (x * a) b, Nat.add_comm x c, pow_add_list, pow_add_list]
  refine hb.trans ?_
  induction x with
  | zero =>
    simp only [Nat.zero_mul, pow_zero_list]
    exact .nil w₂
  | succ x ih =>
    have h₁ : (x + 1) * a = a + x * a := by rw [Nat.succ_mul, Nat.add_comm]
    have h₂ : x + 1 = 1 + x := by omega
    rw [h₁, h₂, pow_add_list, pow_add_list, pow_one_list]
    exact ha.trans ih

theorem SegRLs.addmul_v2 {M : Machine Γ Λ} {h : List (DH0 Γ Λ × DH0 Γ Λ)}
    {a a' x b b' : ℕ} {w₁ w₂ : List Γ}
    (hb : SegRLs M (h ^ b) (h ^ b') w₁ w₂)
    (ha : SegRLs M (h ^ a) (h ^ a') w₂ w₂) :
    SegRLs M (h ^ (x * a + b)) (h ^ (x * a' + b')) w₁ w₂ := by
  rw [Nat.add_comm (x * a) b, Nat.add_comm (x * a') b', pow_add_list, pow_add_list]
  refine hb.trans ?_
  induction x with
  | zero =>
    simp only [Nat.zero_mul, pow_zero_list]
    exact .nil w₂
  | succ x ih =>
    have h₁ : (x + 1) * a = a + x * a := by rw [Nat.succ_mul, Nat.add_comm]
    have h₂ : (x + 1) * a' = a' + x * a' := by rw [Nat.succ_mul, Nat.add_comm]
    rw [h₁, h₂, pow_add_list, pow_add_list]
    exact ha.trans ih

theorem SegRLs.of_segRR_segLLs {M : Machine Γ Λ} {ls₃ ls₄ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ : List Γ} {h₁ h₂ h₃ h₄ : DH0 Γ Λ}
    (h_rr : SegRR M h₁ h₃ w₁ w₃)
    (h_lls : SegLLs M h₂ ls₃ h₄ ls₄ w₃ w₂) :
    SegRLs M ((h₁, h₂) :: ls₃) ((h₃, h₄) :: ls₄) w₁ w₂ := by
  rcases h_lls with ⟨h_lrs, h_ll, h_rls, h_rc⟩
  cases h_lrs with
  | nil _ =>
    injection h_rc with h_eq₁ h_eq₂
    subst h_eq₁ h_eq₂
    exact .lrcons h_rr h_ll (.nil _) h_rls
  | cons h_lr h_lrs_tail =>
    injection h_rc with h_eq₁ h_eq₂
    subst h_eq₁ h_eq₂
    exact .lrcons h_rr h_ll (.cons h_lr h_lrs_tail) h_rls

theorem SegLLs.of_segLR_segLLs {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ : List Γ} {h₁ h₂ h₃ h₄ : DH0 Γ Λ}
    (h_lr : SegLR M h₂ h₃ w₁ w₃)
    (h_lls : SegLLs M h₁ ls₁ h₄ ls₂ w₃ w₂) :
    SegLLs M h₁ ls₁ h₂ ((h₃, h₄) :: ls₂) w₁ w₂ := by
  rcases h_lls with ⟨h_lrs, h_ll, h_rls, h_rc⟩
  cases h_lrs with
  | nil _ =>
    injection h_rc with h₁' h₂'
    subst h₁' h₂'
    change SegLLs M h₁ ls₁ h₂ ([(h₃, _)] ++ _) w₁ w₂
    exact ⟨.cons h_lr (.nil _), h_ll, h_rls, rfl⟩
  | cons h_lr' h_lrs' =>
    injection h_rc with h₁' h₂'
    subst h₁' h₂'
    rw [← List.cons_append]
    exact ⟨.cons h_lr (.cons h_lr' h_lrs'), h_ll, h_rls, rfl⟩

theorem SegLLs.of_segLL_segRLs {M : Machine Γ Λ} {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ w₃ : List Γ} {h₁ h₂ : DH0 Γ Λ}
    (h_ll : SegLL M h₂ h₁ w₁ w₃)
    (h_rls : SegRLs M ls₁ ls₂ w₃ w₂) :
    SegLLs M h₁ ls₁ h₂ ls₂ w₁ w₂ :=
  ⟨.nil w₁, h_ll, h_rls, rfl⟩

-- ============================================================================
-- 6. Halting Dual of the 2D Longitudinal Calculus (`SideRLsHalt`)
-- ============================================================================

private lemma haltsFrom_of_stepStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢* c₂) (hh : ∃ cfg, (c₂ [M]⊢* cfg) ∧ (step M cfg).isNone) :
    ∃ cfg, (c₁ [M]⊢* cfg) ∧ (step M cfg).isNone := by
  obtain ⟨cfg, hreach, hnone⟩ := hh
  exact ⟨cfg, stepStar_trans h hreach, hnone⟩

/-- Companion predicate to `SideRLs` describing a finite right-boundary signal stream whose
execution halts while processing one of its signals (`sideRLs_halt` in `LongitudinalHalt.v`). -/
inductive SideRLsHalt (M : Machine Γ Λ) :
    List (DH0 Γ Λ × DH0 Γ Λ) → ListBlank Γ → Prop where
  | here (hR hL : DH0 Γ Λ) (hs : List (DH0 Γ Λ × DH0 Γ Λ)) (r : ListBlank Γ) :
      (∀ l, ∃ cfg, ((toDHCfg (hR, .right) l r) [M]⊢* cfg) ∧ (step M cfg).isNone) →
      SideRLsHalt M ((hR, hL) :: hs) r
  | next {hR hL : DH0 Γ Λ} {hs : List (DH0 Γ Λ × DH0 Γ Λ)} {r r' : ListBlank Γ} :
      SideRL M hR hL r r' →
      SideRLsHalt M hs r' →
      SideRLsHalt M ((hR, hL) :: hs) r

theorem SideRLsHalt.app_left {M : Machine Γ Λ} {hs₁ hs₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r : ListBlank Γ} (h : SideRLsHalt M hs₁ r) :
    SideRLsHalt M (hs₁ ++ hs₂) r := by
  induction h with
  | here hR hL hs r hh => exact .here hR hL (hs ++ hs₂) r hh
  | next h_rl _ ih => exact .next h_rl ih

theorem SideRLsHalt.app_right {M : Machine Γ Λ} {hs₁ hs₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r r' : ListBlank Γ} (h₁ : SideRLs M hs₁ r r') (h₂ : SideRLsHalt M hs₂ r') :
    SideRLsHalt M (hs₁ ++ hs₂) r := by
  induction h₁ with
  | nil _ => exact h₂
  | cons h_rl _ ih => exact .next h_rl (ih h₂)

theorem SideRLsHalt.split {M : Machine Γ Λ} {hs₁ hs₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r : ListBlank Γ} (h : SideRLsHalt M (hs₁ ++ hs₂) r) :
    SideRLsHalt M hs₁ r ∨ ∃ r', SideRLs M hs₁ r r' ∧ SideRLsHalt M hs₂ r' := by
  induction hs₁ generalizing r with
  | nil => exact Or.inr ⟨r, .nil r, h⟩
  | cons ab hs₁ ih =>
    cases h with
    | here hR hL _ r hh => exact Or.inl (.here hR hL hs₁ r hh)
    | next h_rl h_rest =>
      rcases ih h_rest with h_left | ⟨r', h_side, h_halt⟩
      · exact Or.inl (.next h_rl h_left)
      · exact Or.inr ⟨r', .cons h_rl h_side, h_halt⟩

theorem SideRLsHalt.segLRs_concat {M : Machine Γ Λ} {hs : List (DH0 Γ Λ × DH0 Γ Λ)}
    {h₁ h₂ : DH0 Γ Λ} {w₁ w₂ : List Γ} {r : ListBlank Γ}
    (h_seg : SegLRs M hs w₁ w₂)
    (h_halt : SideRLsHalt M (lrcons h₁ hs h₂) r)
    (l : ListBlank Γ) :
    ∃ cfg, ((toDHCfg (h₁, .right) (w₁ +> l) r) [M]⊢* cfg) ∧ (step M cfg).isNone := by
  induction h_seg generalizing h₁ h₂ r with
  | nil _ =>
    cases h_halt with
    | here _ _ _ _ hh => exact hh (_ +> l)
    | next _ h_empty => cases h_empty
  | cons h_lr _ ih =>
    cases h_halt with
    | here _ _ _ _ hh => exact hh (_ +> l)
    | next h_rl h_rest =>
      exact haltsFrom_of_stepStar
        (stepPlus_to_stepStar (stepPlus_stepStar_trans (h_rl (_ +> l)) (h_lr l _)))
        (ih h_rest)

/-- Backward halting propagation across a 2D longitudinal tile (`segRLs_sideRLs_halt_concat` in
`LongitudinalHalt.v`): if a segment emits a signal stream `hs₂` that halts on `r`, then the input
signal stream `hs₁` halts on `w₁ +> r`. -/
theorem SegRLs.sideRLsHalt_concat {M : Machine Γ Λ} {hs₁ hs₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ : List Γ} {r : ListBlank Γ}
    (h_seg : SegRLs M hs₁ hs₂ w₁ w₂)
    (h_halt : SideRLsHalt M hs₂ r) :
    SideRLsHalt M hs₁ (w₁ +> r) := by
  induction h_seg generalizing r with
  | nil _ => cases h_halt
  | cons h_rl _ ih =>
    exact .next (fun l => h_rl l r) (ih h_halt)
  | lrcons h_rr h_ll h_lrs _ ih =>
    rcases h_halt.split with h_prefix | ⟨r', h_prefix, h_suffix⟩
    · refine .here _ _ _ _ (fun l => ?_)
      exact haltsFrom_of_stepStar (h_rr l r) (h_prefix.segLRs_concat h_lrs l)
    · refine .next (fun l => ?_) (ih h_suffix)
      exact stepStar_stepPlus_trans (h_rr l r)
        (stepPlus_stepStar_trans (h_prefix.segLRs_concat h_lrs l) (h_ll l r'))

theorem SideRLsHalt.elim_single {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {r : ListBlank Γ}
    (h : SideRLsHalt M [(hR, hL)] r) (l : ListBlank Γ) :
    ∃ cfg, ((toDHCfg (hR, .right) l r) [M]⊢* cfg) ∧ (step M cfg).isNone := by
  cases h with
  | here _ _ _ _ hh => exact hh l
  | next _ h_empty => cases h_empty

/-- Glue a mirrored left-half-tape reflection `SideRLs (flipTM M)` with a halting right-half-tape
signal stream `SideRLsHalt M` to prove halting of the full configuration. -/
theorem SideRLsHalt.concat {M : Machine Γ Λ} {h₁ h₂ : DH0 Γ Λ}
    {ls : List (DH0 Γ Λ × DH0 Γ Λ)} {l₁ l₂ r₁ : ListBlank Γ}
    (hl : SideRLs (flipTM M) ls l₁ l₂)
    (hr : SideRLsHalt M (lrcons h₁ ls h₂) r₁) :
    ∃ cfg, ((toDHCfg (h₁, .right) l₁ r₁) [M]⊢* cfg) ∧ (step M cfg).isNone := by
  induction ls generalizing h₁ h₂ l₁ r₁ with
  | nil =>
    exact hr.elim_single l₁
  | cons ab ls ih =>
    rcases ab with ⟨a, b⟩
    cases hl with
    | cons hl_first hl_rest =>
      cases hr with
      | here _ _ _ _ hh => exact hh l₁
      | next hr_first hr_rest =>
        exact haltsFrom_of_stepStar
          (stepPlus_to_stepStar
            (stepPlus_trans (hr_first l₁) (toDHCfg_stepPlus_unflip (hl_first _))))
          (ih hl_rest hr_rest)

-- ============================================================================
-- 7. Unary & Binary Counter Tile Libraries (`UC1`, `UC2`, `UC3`, `BCR`, `BC`)
-- ============================================================================

namespace UC1

theorem incs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₁' : List Γ}
    (h_inc : SegRL M hR hL w₀ w₁)
    (h_ov : SegRR M hR hR w₁ w₁')
    (h_rst : SegLL M hL hL w₁' w₁)
    (n m : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n + m)) ([(hR, hL)] ^ m) (w₀ ^ n) (w₁ ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, pow_zero_list]
    exact SegRLs.empty M _
  | succ n ih =>
    rw [Nat.succ_add, pow_succ_list, pow_succ_list, pow_succ_list]
    refine .cons (fun l r => ?_) ((SegRLs.wall h_ov h_rst _).concat ih)
    rw [append_assoc, append_assoc]
    exact h_inc l (w₀ ^ n +> r)

theorem incs' {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₁' : List Γ}
    (h_inc : SegRL M hR hL w₀ w₁)
    (h_ov : SegRR M hR hR w₁ w₁')
    (h_rst : SegLL M hL hL w₁' w₁)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ n) [] (w₀ ^ n) (w₁ ^ n) :=
  incs h_inc h_ov h_rst n 0

end UC1

namespace UC2

theorem incs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₂ w₂' : List Γ}
    (h_inc₀ : SegRL M hR hL w₀ w₁)
    (h_inc₁ : SegRL M hR hL w₁ w₂)
    (h_ov : SegRR M hR hR w₂ w₂')
    (h_rst : SegLL M hL hL w₂' w₂)
    (n m : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2 + m)) ([(hR, hL)] ^ m) (w₀ ^ n) (w₂ ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, pow_zero_list]
    exact SegRLs.empty M _
  | succ n ih =>
    have h_split : (n + 1) * 2 + m = (n * 2 + m) + 1 + 1 := by omega
    rw [h_split, pow_succ_list, pow_succ_list, pow_succ_list w₀, pow_succ_list w₂]
    have s₀ : SegRL M hR hL (w₀ ++ w₀ ^ n) (w₁ ++ w₀ ^ n) := fun l r => by
      rw [append_assoc, append_assoc]
      exact h_inc₀ l (w₀ ^ n +> r)
    have s₁ : SegRL M hR hL (w₁ ++ w₀ ^ n) (w₂ ++ w₀ ^ n) := fun l r => by
      rw [append_assoc, append_assoc]
      exact h_inc₁ l (w₀ ^ n +> r)
    exact .cons s₀ (.cons s₁ ((SegRLs.wall h_ov h_rst _).concat ih))

theorem incs' {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₂ w₂' : List Γ}
    (h_inc₀ : SegRL M hR hL w₀ w₁)
    (h_inc₁ : SegRL M hR hL w₁ w₂)
    (h_ov : SegRR M hR hR w₂ w₂')
    (h_rst : SegLL M hL hL w₂' w₂)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2)) [] (w₀ ^ n) (w₂ ^ n) :=
  incs h_inc₀ h_inc₁ h_ov h_rst n 0

end UC2

namespace UC3

theorem incs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₂ w₃ w₃' : List Γ}
    (h_inc₀ : SegRL M hR hL w₀ w₁)
    (h_inc₁ : SegRL M hR hL w₁ w₂)
    (h_inc₂ : SegRL M hR hL w₂ w₃)
    (h_ov : SegRR M hR hR w₃ w₃')
    (h_rst : SegLL M hL hL w₃' w₃)
    (n m : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 3 + m)) ([(hR, hL)] ^ m) (w₀ ^ n) (w₃ ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, pow_zero_list]
    exact SegRLs.empty M _
  | succ n ih =>
    have h_split : (n + 1) * 3 + m = (n * 3 + m) + 1 + 1 + 1 := by omega
    rw [h_split, pow_succ_list, pow_succ_list, pow_succ_list, pow_succ_list w₀, pow_succ_list w₃]
    have s₀ : SegRL M hR hL (w₀ ++ w₀ ^ n) (w₁ ++ w₀ ^ n) := fun l r => by
      rw [append_assoc, append_assoc]
      exact h_inc₀ l (w₀ ^ n +> r)
    have s₁ : SegRL M hR hL (w₁ ++ w₀ ^ n) (w₂ ++ w₀ ^ n) := fun l r => by
      rw [append_assoc, append_assoc]
      exact h_inc₁ l (w₀ ^ n +> r)
    have s₂ : SegRL M hR hL (w₂ ++ w₀ ^ n) (w₃ ++ w₀ ^ n) := fun l r => by
      rw [append_assoc, append_assoc]
      exact h_inc₂ l (w₀ ^ n +> r)
    exact .cons s₀ (.cons s₁ (.cons s₂ ((SegRLs.wall h_ov h_rst _).concat ih)))

theorem incs' {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w₀ w₁ w₂ w₃ w₃' : List Γ}
    (h_inc₀ : SegRL M hR hL w₀ w₁)
    (h_inc₁ : SegRL M hR hL w₁ w₂)
    (h_inc₂ : SegRL M hR hL w₂ w₃)
    (h_ov : SegRR M hR hR w₃ w₃')
    (h_rst : SegLL M hL hL w₃' w₃)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 3)) [] (w₀ ^ n) (w₃ ^ n) :=
  incs h_inc₀ h_inc₁ h_inc₂ h_ov h_rst n 0

end UC3

namespace BCR

theorem incs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_lr : SegLR M hL hR d₀ d₁)
    (h_carry : SegLL M hL hL d₁ d₁')
    (h_ret : SegRR M hR hR d₁' d₀)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ n) ([(hR, hL)] ^ (n * 2)) d₁' d₁' := by
  induction n with
  | zero => exact .nil d₁'
  | succ n ih =>
    have h_mul : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [pow_succ_list, h_mul, pow_add_list]
    exact .lrcons h_ret h_carry (.cons h_lr (.nil d₁)) ih

end BCR

namespace BC

theorem incs' {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2 + 1)) ([(hR, hL)] ^ n) d₀ d₁ := by
  induction n with
  | zero => exact .cons h_rl (.nil d₁)
  | succ n ih =>
    have h_eq : (n + 1) * 2 + 1 = 2 + (n * 2 + 1) := by omega
    rw [h_eq, pow_add_list, pow_succ_list ([(hR, hL)]) n]
    exact (SegRLs.cons h_rl (SegRLs.S' h_carry h_ret (.nil d₀))).trans ih

theorem incsOvs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n m : ℕ) :
    SegRLs M ([(hR, hL)] ^ ((n + 1) * 2 ^ m - 1)) ([(hR, hL)] ^ n) (d₀ ^ m) (d₁ ^ m) := by
  induction m generalizing n with
  | zero =>
    have h_eq : (n + 1) * 2 ^ 0 - 1 = n := by omega
    rw [h_eq, pow_zero_list, pow_zero_list]
    exact SegRLs.empty M _
  | succ m ih =>
    have h_pos : (n + 1) * 2 ^ m > 0 := Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos m)
    have h_eq : (n + 1) * 2 ^ (m + 1) - 1 = ((n + 1) * 2 ^ m - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega
    rw [h_eq, pow_succ_list d₀, pow_succ_list d₁]
    exact (incs' h_rl h_carry h_ret ((n + 1) * 2 ^ m - 1)).concat (ih n)

theorem mul2 {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2)) ([(hR, hL)] ^ n) d₁ d₁ := by
  induction n with
  | zero => exact .nil d₁
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, pow_add_list, pow_succ_list ([(hR, hL)]) n]
    exact SegRLs.S' h_carry h_ret (.cons h_rl ih)

theorem ovs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n m : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2 ^ m)) ([(hR, hL)] ^ n) (d₁ ^ m) (d₁ ^ m) := by
  induction m generalizing n with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact SegRLs.empty M _
  | succ m ih =>
    have h_eq : n * 2 ^ (m + 1) = (n * 2 ^ m) * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [h_eq, pow_succ_list d₁]
    exact (mul2 h_rl h_carry h_ret (n * 2 ^ m)).concat (ih n)

theorem incs {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (2 ^ n - 1)) [] (d₀ ^ n) (d₁ ^ n) := by
  simpa using incsOvs h_rl h_carry h_ret 0 n

theorem incsMul2 {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {d₀ d₁ d₁' : List Γ}
    (h_rl : SegRL M hR hL d₀ d₁)
    (h_carry : SegRR M hR hR d₁ d₁')
    (h_ret : SegLL M hL hL d₁' d₀)
    (n : ℕ) :
    SegRLs M ([(hR, hL)] ^ (2 ^ n * 2 - 2)) [] (d₁ ++ d₀ ^ n) (d₁ ++ d₁ ^ n) := by
  have h_pos : 2 ^ n > 0 := Nat.two_pow_pos n
  have h_eq : 2 ^ n * 2 - 2 = (2 ^ n - 1) * 2 := by omega
  rw [h_eq]
  exact (mul2 h_rl h_carry h_ret (2 ^ n - 1)).concat (incs h_rl h_carry h_ret n)

end BC

-- ============================================================================
-- 8. Parametric Shift-Overflow Binary Counter Closure (`SBC`)
-- ============================================================================

namespace SBC

def RC0 (w u z : List Γ) (a n m : ℕ) : ListBlank Γ :=
  w ^ a +> (z +> (w ^ n +> (u ^ m +> default)))

def RC1 (w v : List Γ) (a m : ℕ) : ListBlank Γ :=
  w ^ (a + 1) +> (v ^ m +> default)

def RC2 (w u : List Γ) (a m : ℕ) : ListBlank Γ :=
  w ^ (a + 1) +> (u ^ m +> default)

lemma RC2_head (w u : List Γ) (a m : ℕ) :
    RC2 w u a m = w +> (w ^ a +> (u ^ m +> default)) := by
  unfold RC2
  rw [pow_succ_list, append_assoc]

/-- Parametric Shift-Overflow Binary Counter rule specification (`SBCv13.v`). -/
structure Rules (M : Machine Γ Λ) (hR hL : DH0 Γ Λ)
    (w u v z d₀ d₁ d₁' : List Γ) (dh : ListBlank Γ) : Prop where
  rule_wall : SegRLs M ([(hR, hL)] ^ 2) ([(hR, hL)] ^ 2) w w
  rule_pair : SegRLs M ([(hR, hL)] ^ 6) ([(hR, hL)] ^ 2) (z ++ w ++ w) (w ++ w ++ z)
  rule_R : ∀ n m, SideRLs M ([(hR, hL)] ^ 6) (RC0 w u z 0 (2 + n) m) (RC0 w u z 2 n (1 + m))
  rule_U : ∀ m, SideRLs M ([(hR, hL)] ^ 4) (RC0 w u z 0 0 (1 + m)) (RC0 w u z 1 0 m)
  rule_odd : ∀ m, SideRLs M ([(hR, hL)] ^ 2) (RC0 w u z 0 1 m) (RC1 w v 0 (1 + m))
  rule_V : ∀ m, SideRLs M ([(hR, hL)] ^ 2) (RC1 w v 0 (1 + m)) (RC1 w v 1 m)
  rule_empty : SideRLs M ([(hR, hL)] ^ 4) (RC0 w u z 0 0 0) (RC2 w u 1 0)
  rule_grow : ∀ m, SideRLs M ([(hR, hL)] ^ 2) (RC2 w u 0 m) (RC2 w u 0 (1 + m))
  rule_reset : ∀ k r,
    (toDHCfg (hL, .left) (d₁ ^ (1 + k) +> dh) (w +> r)) [M]⊢*
      (toDHCfg (hR, .right) (d₀ +> (d₁ +> (d₀ ^ k +> dh))) (z +> r))
  rule_zero : SegRL (flipTM M) hL hR d₀ d₁
  rule_carry : SegRR (flipTM M) hL hL d₁ d₁'
  rule_return : SegLL (flipTM M) hR hR d₁' d₀

section WithRules

variable {M : Machine Γ Λ} {hR hL : DH0 Γ Λ} {w u v z d₀ d₁ d₁' : List Γ} {dh : ListBlank Γ}

def G (M : Machine Γ Λ) (hR hL : DH0 Γ Λ) (n : ℕ) (r s : ListBlank Γ) : Prop :=
  SideRLs M ([(hR, hL)] ^ n) r s

def CfgAt (hR : DH0 Γ Λ) (d₀ d₁ : List Γ) (dh : ListBlank Γ) (k : ℕ) (r : ListBlank Γ) :
    Cfg Γ Λ :=
  toDHCfg (hR, .right) (d₀ +> (d₁ +> (d₀ ^ k +> dh))) r

def S (hR : DH0 Γ Λ) (w u z d₀ d₁ : List Γ) (dh : ListBlank Γ) (k n m : ℕ) : Cfg Γ Λ :=
  CfgAt hR d₀ d₁ dh k (RC0 w u z 0 n m)

lemma G_add {a b : ℕ} {r s t : ListBlank Γ}
    (h₁ : G M hR hL a r s) (h₂ : G M hR hL b s t) :
    G M hR hL (a + b) r t :=
  SideRLs.trans_add h₁ h₂

lemma G_split {a b : ℕ} {r t : ListBlank Γ}
    (h : G M hR hL (a + b) r t) :
    ∃ s, G M hR hL a r s ∧ G M hR hL b s t := by
  unfold G at h ⊢
  rw [pow_add_list] at h
  exact h.split

lemma wp (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (n a : ℕ) :
    SegRLs M ([(hR, hL)] ^ (n * 2)) ([(hR, hL)] ^ (n * 2)) (w ^ a) (w ^ a) := by
  induction a with
  | zero => exact SegRLs.empty M _
  | succ a ih =>
    rw [pow_succ_list w, Nat.mul_comm n 2, pow_mul_list]
    exact (rules.rule_wall.wall_pow n).concat (by rw [← pow_mul_list, Nat.mul_comm 2 n]; exact ih)

lemma G_w (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (n a : ℕ) {r s : ListBlank Γ}
    (h : G M hR hL (n * 2) r s) :
    G M hR hL (n * 2) (w ^ a +> r) (w ^ a +> s) :=
  (wp rules n a).sideRLs_concat h

lemma pair (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (a : ℕ) :
    SegRLs M ([(hR, hL)] ^ 6) ([(hR, hL)] ^ 2) (z ++ w ^ (2 + a)) (w ^ 2 ++ z ++ w ^ a) := by
  have h₁ : z ++ w ^ (2 + a) = (z ++ w ++ w) ++ w ^ a := by
    have h_add : 2 + a = a + 1 + 1 := by omega
    rw [h_add, pow_succ_list, pow_succ_list, List.append_assoc, List.append_assoc]
  have h₂ : w ^ 2 ++ z ++ w ^ a = (w ++ w ++ z) ++ w ^ a := by
    change (w ++ (w ++ [])) ++ z ++ w ^ a = (w ++ w ++ z) ++ w ^ a
    simp only [List.append_nil, List.append_assoc]
  rw [h₁, h₂]
  exact rules.rule_pair.concat (wp rules 1 a)

lemma peel (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (n a : ℕ) {r s : ListBlank Γ}
    (h : G M hR hL (n * 2) r s) :
    G M hR hL (n * 6) (z +> (w ^ (n * 2 + a) +> r)) (w ^ (n * 2) +> (z +> (w ^ a +> s))) := by
  induction n generalizing r s with
  | zero =>
    cases h
    simp only [G, Nat.zero_mul, Nat.zero_add, pow_zero_list, append_nil]
    exact .nil _
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq] at h
    obtain ⟨t, h₂, hn⟩ := G_split h
    have h_eq6 : (n + 1) * 6 = 6 + n * 6 := by omega
    rw [h_eq6]
    refine G_add (s := w ^ 2 +> (z +> (w ^ (n * 2 + a) +> t))) ?_ ?_
    · have h_p := (pair rules (n * 2 + a)).sideRLs_concat h₂
      have h_lhs : (z ++ w ^ (2 + (n * 2 + a))) +> r = z +> (w ^ ((n + 1) * 2 + a) +> r) := by
        rw [append_assoc, h_eq, Nat.add_assoc]
      have h_rhs : (w ^ 2 ++ z ++ w ^ (n * 2 + a)) +> t =
          w ^ 2 +> (z +> (w ^ (n * 2 + a) +> t)) := by
        rw [List.append_assoc, append_assoc, append_assoc]
      rwa [h_lhs, h_rhs] at h_p
    · have h_rec := G_w rules (n * 3) 2 (by
        have h3 : n * 3 * 2 = n * 6 := by omega
        rw [h3]
        exact ih hn)
      have h3 : n * 3 * 2 = n * 6 := by omega
      rw [h3, ← append_assoc (w ^ 2) (w ^ (n * 2)), ← pow_add_list, ← h_eq] at h_rec
      exact h_rec

lemma R_steps (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (k a n m : ℕ) :
    G M hR hL (k * 6) (RC0 w u z a (k * 2 + n) m) (RC0 w u z (a + k * 2) n (m + k)) := by
  induction k generalizing a n m with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    have h_eq : (k + 1) * 6 = 6 + k * 6 := by omega
    rw [h_eq]
    refine G_add (s := RC0 w u z (a + 2) (k * 2 + n) (1 + m)) ?_ ?_
    · have hw := G_w rules 3 a (rules.rule_R (k * 2 + n) m)
      unfold RC0 at hw ⊢
      rw [← append_assoc (w ^ a) (w ^ 0), ← append_assoc (w ^ a) (w ^ 2),
        ← pow_add_list, ← pow_add_list, Nat.add_zero] at hw
      have h_k : (k + 1) * 2 + n = 2 + (k * 2 + n) := by omega
      rwa [h_k]
    · have ih' := ih (a + 2) n (1 + m)
      have h₁ : a + 2 + k * 2 = a + (k + 1) * 2 := by omega
      have h₂ : 1 + m + k = m + (k + 1) := by omega
      rwa [h₁, h₂] at ih'

lemma U_steps (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (k a m : ℕ) :
    G M hR hL (k * 4) (RC0 w u z a 0 (k + m)) (RC0 w u z (a + k) 0 m) := by
  induction k generalizing a m with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    have h_eq : (k + 1) * 4 = 4 + k * 4 := by omega
    rw [h_eq]
    refine G_add (s := RC0 w u z (a + 1) 0 (k + m)) ?_ ?_
    · have hw := G_w rules 2 a (rules.rule_U (k + m))
      unfold RC0 at hw ⊢
      rw [← append_assoc (w ^ a) (w ^ 0), ← append_assoc (w ^ a) (w ^ 1),
        ← pow_add_list, ← pow_add_list, Nat.add_zero] at hw
      have h_k : k + 1 + m = 1 + (k + m) := by omega
      rwa [h_k]
    · have ih' := ih (a + 1) m
      have h₁ : a + 1 + k = a + (k + 1) := by omega
      rwa [h₁] at ih'

lemma V_steps (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (k a m : ℕ) :
    G M hR hL (k * 2) (RC1 w v a (k + m)) (RC1 w v (a + k) m) := by
  induction k generalizing a m with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    have h_eq : (k + 1) * 2 = 2 + k * 2 := by omega
    rw [h_eq]
    refine G_add (s := RC1 w v (a + 1) (k + m)) ?_ ?_
    · have hw := G_w rules 1 a (rules.rule_V (k + m))
      unfold RC1 at hw ⊢
      rw [← append_assoc (w ^ a) (w ^ (0 + 1)), ← append_assoc (w ^ a) (w ^ (1 + 1)),
        ← pow_add_list, ← pow_add_list, Nat.zero_add] at hw
      have h_k : k + 1 + m = 1 + (k + m) := by omega
      have h_a : a + 1 + 1 = a + (1 + 1) := by omega
      rwa [h_k, h_a]
    · have ih' := ih (a + 1) m
      have h₁ : a + 1 + k = a + (k + 1) := by omega
      rwa [h₁] at ih'

lemma grow_steps (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (k a m : ℕ) :
    G M hR hL (k * 2) (RC2 w u a m) (RC2 w u a (m + k)) := by
  induction k generalizing m with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    have h_eq : (k + 1) * 2 = 2 + k * 2 := by omega
    rw [h_eq]
    refine G_add (s := RC2 w u a (1 + m)) ?_ ?_
    · have hw := G_w rules 1 a (rules.rule_grow m)
      unfold RC2 at hw ⊢
      rw [← append_assoc (w ^ a) (w ^ (0 + 1)), ← append_assoc (w ^ a) (w ^ (0 + 1)),
        ← pow_add_list, Nat.zero_add] at hw
      exact hw
    · have ih' := ih (1 + m)
      have h₁ : 1 + m + k = m + (k + 1) := by omega
      rwa [h₁] at ih'

lemma normal_odd (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (a n m t : ℕ) :
    G M hR hL (n * 8 + m * 2 + 4 + t * 2)
      (RC0 w u z a (n * 2 + 1) m) (RC2 w u (a + 1 + n * 3 + m) t) := by
  have h_eq : n * 8 + m * 2 + 4 + t * 2 = n * 6 + (2 + ((1 + m + n) * 2 + t * 2)) := by omega
  rw [h_eq]
  refine G_add (R_steps rules n a 1 m) (G_add (s := RC1 w v (a + n * 2) (1 + m + n)) ?_ ?_)
  · have hw := G_w rules 1 (a + n * 2) (rules.rule_odd (m + n))
    unfold RC0 RC1 at hw ⊢
    rw [← append_assoc (w ^ (a + n * 2)) (w ^ 0),
      ← append_assoc (w ^ (a + n * 2)) (w ^ (0 + 1)),
      ← pow_add_list, ← pow_add_list, Nat.add_zero, Nat.zero_add,
      ← Nat.add_assoc 1 m n] at hw
    exact hw
  · refine G_add (s := RC1 w v (a + n * 2 + (1 + m + n)) 0) ?_ ?_
    · have hv := V_steps rules (1 + m + n) (a + n * 2) 0
      rwa [Nat.add_zero] at hv
    · have h_rc : RC1 w v (a + n * 2 + (1 + m + n)) 0 = RC2 w u (a + 1 + n * 3 + m) 0 := by
        unfold RC1 RC2
        have h_idx : a + n * 2 + (1 + m + n) + 1 = a + 1 + n * 3 + m + 1 := by omega
        rw [h_idx, pow_zero_list, pow_zero_list]
      rw [h_rc]
      have hg := grow_steps rules t (a + 1 + n * 3 + m) 0
      rwa [Nat.zero_add] at hg

lemma normal_even (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (a n m t : ℕ) :
    G M hR hL (n * 10 + m * 4 + 4 + t * 2)
      (RC0 w u z a (n * 2) m) (RC2 w u (a + 1 + n * 3 + m) t) := by
  have h_eq : n * 10 + m * 4 + 4 + t * 2 = n * 6 + ((m + n) * 4 + (4 + t * 2)) := by omega
  rw [h_eq]
  have hR0 := R_steps rules n a 0 m
  rw [Nat.add_zero] at hR0
  refine G_add hR0 (G_add (s := RC0 w u z (a + n * 2 + (m + n)) 0 0) ?_ ?_)
  · have hU := U_steps rules (m + n) (a + n * 2) 0
    rwa [Nat.add_zero] at hU
  · refine G_add (s := RC2 w u (a + n * 2 + (m + n) + 1) 0) ?_ ?_
    · have hw := G_w rules 2 (a + n * 2 + (m + n)) rules.rule_empty
      unfold RC0 RC2 at hw ⊢
      rw [← append_assoc (w ^ (a + n * 2 + (m + n))) (w ^ 0),
        ← append_assoc (w ^ (a + n * 2 + (m + n))) (w ^ (1 + 1)),
        ← pow_add_list, ← pow_add_list, Nat.add_zero,
        ← Nat.add_assoc (a + n * 2 + (m + n)) 1 1] at hw
      exact hw
    · have h_idx : a + n * 2 + (m + n) + 1 = a + 1 + n * 3 + m := by omega
      rw [h_idx]
      have hg := grow_steps rules t (a + 1 + n * 3 + m) 0
      rwa [Nat.zero_add] at hg

lemma left_incs (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (n : ℕ) :
    SideRLs (flipTM M) ([(hL, hR)] ^ ((2 ^ n - 1) * 2 * 2 + 1))
      (d₀ +> (d₁ +> (d₀ ^ n +> dh)))
      (d₁ +> (d₁ +> (d₁ ^ n +> dh))) :=
  (BC.incs' rules.rule_zero rules.rule_carry rules.rule_return ((2 ^ n - 1) * 2)).sideRLs_concat
    ((BC.mul2 rules.rule_zero rules.rule_carry rules.rule_return (2 ^ n - 1)).sideRLs_concat
      ((BC.incs rules.rule_zero rules.rule_carry rules.rule_return n).sideRLs_concat (.nil dh)))

lemma round (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) {k n : ℕ} {r s : ListBlank Γ}
    (hn : n + 2 = 2 ^ k * 4)
    (hG : G M hR hL n r (w +> s)) :
    (CfgAt hR d₀ d₁ dh k r) [M]⊢⁺ (CfgAt hR d₀ d₁ dh (k + 1) (z +> s)) := by
  have h_pos : 2 ^ k > 0 := Nat.two_pow_pos k
  have h_idx : (2 ^ k - 1) * 2 * 2 + 1 + 1 = n := by omega
  have hr : SideRLs M (lrcons hR ([(hL, hR)] ^ ((2 ^ k - 1) * 2 * 2 + 1)) hL) r (w +> s) := by
    rw [lrcons_same, h_idx]
    exact hG
  have h_step₁ := SideRLs.concat (left_incs rules k) hr
  have h_lhs : d₁ +> (d₁ +> (d₁ ^ k +> dh)) = d₁ ^ (1 + (k + 1)) +> dh := by
    have h_p : 1 + (k + 1) = k + 1 + 1 := by omega
    rw [h_p, pow_succ_list, pow_succ_list, append_assoc, append_assoc]
  rw [h_lhs] at h_step₁
  exact stepPlus_stepStar_trans h_step₁ (rules.rule_reset (k + 1) s)

def need (n m : ℕ) (odd : Bool) : ℕ :=
  if odd then n * 8 + m * 2 + 4 else n * 10 + m * 4 + 4

lemma normal (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) (a n m : ℕ) (odd : Bool) (t : ℕ) :
    G M hR hL (need n m odd + t * 2)
      (RC0 w u z a (n * 2 + if odd then 1 else 0) m)
      (RC2 w u (a + 1 + n * 3 + m) t) := by
  cases odd
  · simpa [need] using normal_even rules a n m t
  · simpa [need] using normal_odd rules a n m t

lemma normal_round (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh)
    (k n m : ℕ) (odd : Bool) (t : ℕ)
    (h_clock : need n m odd + t * 2 + 2 = 2 ^ k * 4) :
    (S hR w u z d₀ d₁ dh k (n * 2 + if odd then 1 else 0) m) [M]⊢⁺
      (S hR w u z d₀ d₁ dh (k + 1) (1 + n * 3 + m) t) := by
  unfold S
  have h_norm := normal rules 0 n m odd t
  rw [Nat.zero_add, RC2_head] at h_norm
  exact round rules h_clock h_norm

lemma recovery (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh)
    (k a b c e q r d n : ℕ) (odd : Bool) (t m : ℕ)
    (h_clock₁ : a * 6 + b * 4 + e * 2 + 2 = 2 ^ k * 4)
    (h_zero : m + a = b + c)
    (h_prefix : a * 2 + b = 1 + q * 2 + r)
    (h_tail : c * 4 + 4 + d * 2 = (e + q) * 2)
    (h_parity : r + c + 2 = n * 2 + if odd then 1 else 0)
    (h_clock₂ : q * 6 + need n d odd + t * 2 + 2 = 2 ^ (k + 1) * 4) :
    (S hR w u z d₀ d₁ dh k (a * 2) m) [M]⊢⁺
      (S hR w u z d₀ d₁ dh (k + 2) (q * 2 + 1 + n * 3 + d) t) := by
  have h_even : G M hR hL (e * 2 + q * 2) (RC0 w u z 0 0 c) (RC2 w u (c + 1) d) := by
    have h₀ := normal_even rules 0 0 c d
    have h_cnt : 0 * 10 + c * 4 + 4 + d * 2 = e * 2 + q * 2 := by omega
    have h_idx : 0 + 1 + 0 * 3 + c = c + 1 := by omega
    rwa [h_cnt, h_idx] at h₀
  obtain ⟨X, he, hq⟩ := G_split h_even
  refine stepPlus_trans (c₂ := CfgAt hR d₀ d₁ dh (k + 1) (z +> (w ^ (q * 2 + r) +> X))) ?_ ?_
  · unfold S
    refine round rules (n := a * 6 + (b * 4 + e * 2)) (by omega) ?_
    refine G_add (s := RC0 w u z (a * 2) 0 (m + a)) ?_ ?_
    · have hR0 := R_steps rules a 0 0 m
      rwa [Nat.zero_add, Nat.add_zero] at hR0
    · refine G_add (s := RC0 w u z (a * 2 + b) 0 c) ?_ ?_
      · have hU := U_steps rules b (a * 2) c
        rwa [← h_zero] at hU
      · have h_we := G_w rules e (a * 2 + b) he
        unfold RC0 at h_we ⊢
        rw [pow_zero_list, append_nil] at h_we
        have h_w_split : w ^ (a * 2 + b) +> X = w +> (w ^ (q * 2 + r) +> X) := by
          have h_p : a * 2 + b = (q * 2 + r) + 1 := by omega
          rw [h_p, pow_succ_list, append_assoc]
        rwa [h_w_split] at h_we
  · unfold S
    have h_k2 : k + 2 = (k + 1) + 1 := by omega
    rw [h_k2]
    refine round rules (n := q * 6 + (need n d odd + t * 2)) (by omega) ?_
    refine G_add (s := RC0 w u z (q * 2) (r + c + 2) d) ?_ ?_
    · have hp := peel rules q r hq
      unfold RC2 at hp
      unfold RC0
      have h_w_c : w ^ (r + (c + 1 + 1)) +> (u ^ d +> default) =
          w ^ (r + c + 2) +> (u ^ d +> default) := by
        have h_rc : r + (c + 1 + 1) = r + c + 2 := by omega
        rw [h_rc]
      rwa [← append_assoc (w ^ r) (w ^ (c + 1 + 1)), ← pow_add_list, h_w_c] at hp
    · rw [h_parity]
      have hn := normal rules (q * 2) n d odd t
      rw [RC2_head] at hn
      exact hn

lemma closed (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh) {k n m : ℕ}
    (hk : 2 ≤ k) (hsum : n + m + 2 ≤ 2 ^ k) :
    ∃ k' n' m',
      ((S hR w u z d₀ d₁ dh k n m) [M]⊢⁺ (S hR w u z d₀ d₁ dh k' n' m')) ∧
      2 ≤ k' ∧ n' + m' + 2 ≤ 2 ^ k' := by
  have hT : 4 ≤ 2 ^ k := by
    have h2 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    exact h2
  have h_pow1 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
  have h_pow2 : 2 ^ (k + 2) = 2 ^ k * 4 := by
    rw [Nat.pow_succ, h_pow1]
    omega
  set a := n / 2
  have hn_div : n = a * 2 + n % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with hn_even | hn_odd
  · rw [hn_even, Nat.add_zero] at hn_div
    by_cases hgood : a * 5 + m * 2 + 3 ≤ 2 ^ k * 2
    · set t := 2 ^ k * 2 - a * 5 - m * 2 - 3
      refine ⟨k + 1, 1 + a * 3 + m, t, ?_, by omega, by omega⟩
      have hn0 : n = a * 2 + if false then 1 else 0 := by dsimp; omega
      rw [hn0]
      exact normal_round rules k a m false t (by dsimp [need]; omega)
    · set D := 2 ^ k * 2 - 1 - a * 3
      set b := D / 2
      set e := D % 2
      set c := m + a - b
      set q := (a * 2 + b - 1) / 2
      set r := (a * 2 + b - 1) % 2
      set d := q + e - c * 2 - 2
      set v' := (r + c + 2) / 2
      rcases Nat.mod_two_eq_zero_or_one (r + c + 2) with hs0 | hs1
      · set h_need := v' * 5 + d * 2 + 2
        set t := 2 ^ k * 4 - q * 3 - h_need - 1
        refine ⟨k + 2, q * 2 + 1 + v' * 3 + d, t, ?_, by omega, by omega⟩
        rw [hn_div]
        refine recovery rules k a b c e q r d v' false t m
          (by omega) (by omega) (by omega) (by omega) (by dsimp; omega) ?_
        dsimp [need]
        omega
      · set h_need := v' * 4 + d + 2
        set t := 2 ^ k * 4 - q * 3 - h_need - 1
        refine ⟨k + 2, q * 2 + 1 + v' * 3 + d, t, ?_, by omega, by omega⟩
        rw [hn_div]
        refine recovery rules k a b c e q r d v' true t m
          (by omega) (by omega) (by omega) (by omega) (by dsimp; omega) ?_
        dsimp [need]
        omega
  · rw [hn_odd] at hn_div
    set t := 2 ^ k * 2 - a * 4 - m - 3
    refine ⟨k + 1, 1 + a * 3 + m, t, ?_, by omega, by omega⟩
    have hn1 : n = a * 2 + if true then 1 else 0 := by dsimp; omega
    rw [hn1]
    exact normal_round rules k a m true t (by dsimp [need]; omega)

/-- Prove `IsDoesNotHalt M` from an initial reachability witness into `SBC.S` and `SBC.Rules`. -/
theorem does_not_halt (rules : Rules M hR hL w u v z d₀ d₁ d₁' dh)
    {k₀ n₀ m₀ : ℕ}
    (h_init : (init []) [M]⊢* (S hR w u z d₀ d₁ dh k₀ n₀ m₀))
    (hk₀ : 2 ≤ k₀) (hsum₀ : n₀ + m₀ + 2 ≤ 2 ^ k₀) :
    IsDoesNotHalt M := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ k n m, c = S hR w u z d₀ d₁ dh k n m ∧ 2 ≤ k ∧ n + m + 2 ≤ 2 ^ k)
    ⟨S hR w u z d₀ d₁ dh k₀ n₀ m₀, h_init, k₀, n₀, m₀, rfl, hk₀, hsum₀⟩ ?_
  rintro _ ⟨k, n, m, rfl, hk, hsum⟩
  obtain ⟨k', n', m', h_step, hk', hsum'⟩ := closed rules hk hsum
  exact ⟨S hR w u z d₀ d₁ dh k' n' m', h_step, k', n', m', rfl, hk', hsum'⟩

end WithRules

end SBC

-- ============================================================================
-- 9. Reflective 2D Longitudinal Tile & Half-Tape Checker (`BoundedConfig`)
-- ============================================================================

namespace BoundedConfig

/-- Bounded finite-window directed configuration (`BoundedConfig.T` in `Individual.v`). -/
structure BCfg (Γ Λ : Type*) where
  l : List Γ
  r : List Γ
  s : Λ
  sgn : Dir
deriving DecidableEq

/-- Realize `BCfg` between arbitrary half-tapes `l₀` and `r₀`. -/
def toCfg (x : BCfg Γ Λ) (l₀ r₀ : ListBlank Γ) : Cfg Γ Λ :=
  match x.sgn with
  | .left => (x.r +> l₀) <{{x.s}} (x.l +> r₀)
  | .right => (x.l +> l₀) {{x.s}}> (x.r +> r₀)

section Decidable

variable [DecidableEq Γ] [DecidableEq Λ]

/-- Execute one bounded step inside `x.r` (`BoundedConfig.step` in `Individual.v`). -/
def step (M : Machine Γ Λ) (x : BCfg Γ Λ) : Option (BCfg Γ Λ) :=
  match x.r with
  | [] => none
  | m :: r₀ =>
    match M x.s m with
    | none => none
    | some (none, _) => none
    | some (some s', Stmt.write m' sgn') =>
      if x.sgn == sgn' then
        some ⟨m' :: x.l, r₀, s', sgn'⟩
      else
        some ⟨m' :: r₀, x.l, s', sgn'⟩

/-- Iterate `step` up to `n` times until `x.r` is exhausted (`BoundedConfig.steps`). -/
def steps (M : Machine Γ Λ) : ℕ → BCfg Γ Λ → Option (BCfg Γ Λ)
  | 0, x =>
    match step M x with
    | none => some x
    | some _ => none
  | n + 1, x =>
    match step M x with
    | none => some x
    | some x' => steps M n x'

/-- Run `steps` while recording whether at least one transition occurred (`BoundedConfig.steps1`). -/
def steps1 (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) : Option (BCfg Γ Λ × Bool) :=
  match step M x with
  | none => some (x, false)
  | some x' => (steps M n x').map (fun y => (y, true))

/-- Execute one bounded step where a rightward head at `r = []` extends into the blank right
half-tape (`BoundedConfig.step_r0inf`). -/
def step_r0inf (M : Machine Γ Λ) (x : BCfg Γ Λ) : Option (BCfg Γ Λ) :=
  match x.r with
  | [] =>
    match x.sgn with
    | .right =>
      match M x.s default with
      | none => none
      | some (none, _) => none
      | some (some s', Stmt.write m' sgn') =>
        if x.sgn == sgn' then
          some ⟨m' :: x.l, [], s', sgn'⟩
        else
          some ⟨[m'], x.l, s', sgn'⟩
    | .left => none
  | m :: r₀ =>
    match M x.s m with
    | none => none
    | some (none, _) => none
    | some (some s', Stmt.write m' sgn') =>
      if x.sgn == sgn' then
        some ⟨m' :: x.l, r₀, s', sgn'⟩
      else
        some ⟨m' :: r₀, x.l, s', sgn'⟩

/-- Iterate `step_r0inf` up to `n` times until the head exits left (`BoundedConfig.steps_r0inf`). -/
def steps_r0inf (M : Machine Γ Λ) : ℕ → BCfg Γ Λ → Option (BCfg Γ Λ)
  | 0, x =>
    match step_r0inf M x with
    | none => some x
    | some _ => none
  | n + 1, x =>
    match step_r0inf M x with
    | none => some x
    | some x' => steps_r0inf M n x'

/-- Run at least one `step_r0inf` followed by `steps_r0inf` (`BoundedConfig.steps1_r0inf`). -/
def steps1_r0inf (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) : Option (BCfg Γ Λ) :=
  match step_r0inf M x with
  | none => none
  | some x' => steps_r0inf M n x'

theorem step_spec (M : Machine Γ Λ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : step M x = some x') (l₀ r₀ : ListBlank Γ) :
    (toCfg x l₀ r₀) [M]⊢ (toCfg x' l₀ r₀) := by
  rcases x with ⟨l₁, _ | ⟨m, r₁⟩, s₁, sgn₁⟩
  · cases h
  · dsimp [step] at h
    rcases hM : M s₁ m with _ | ⟨_ | s₂, ⟨m₂, sgn₂⟩⟩ <;> rw [hM] at h
    · cases h
    · cases h
    · rcases sgn₁ <;> rcases sgn₂ <;> cases h <;>
        simp [toCfg, BusyBeaver.step, hM, Tape.write, Tape.move]

theorem step_r0inf_spec (M : Machine Γ Λ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : step_r0inf M x = some x') (l₀ : ListBlank Γ) :
    (toCfg x l₀ default) [M]⊢ (toCfg x' l₀ default) := by
  rcases x with ⟨l₁, _ | ⟨m, r₁⟩, s₁, sgn₁⟩
  · rcases sgn₁
    · cases h
    · dsimp [step_r0inf] at h
      rcases hM : M s₁ default with _ | ⟨_ | s₂, ⟨m₂, sgn₂⟩⟩ <;> rw [hM] at h
      · cases h
      · cases h
      · rcases sgn₂ <;> cases h <;>
          simp [toCfg, BusyBeaver.step, hM, Tape.write, Tape.move,
            default_head, default_tail]
  · dsimp [step_r0inf] at h
    rcases hM : M s₁ m with _ | ⟨_ | s₂, ⟨m₂, sgn₂⟩⟩ <;> rw [hM] at h
    · cases h
    · cases h
    · rcases sgn₁ <;> rcases sgn₂ <;> cases h <;>
        simp [toCfg, BusyBeaver.step, hM, Tape.write, Tape.move]

theorem steps_spec (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : steps M n x = some x') (l₀ r₀ : ListBlank Γ) :
    (toCfg x l₀ r₀) [M]⊢* (toCfg x' l₀ r₀) := by
  induction n generalizing x with
  | zero =>
    dsimp [steps] at h
    rcases hstep : step M x with _ | y <;> rw [hstep] at h
    · cases h
      exact stepStar_refl M _
    · cases h
  | succ n ih =>
    dsimp [steps] at h
    rcases hstep : step M x with _ | y <;> rw [hstep] at h
    · cases h
      exact stepStar_refl M _
    · exact stepStar_trans ⟨1, step_spec M x hstep l₀ r₀⟩ (ih y h)

theorem steps_r0inf_spec (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : steps_r0inf M n x = some x') (l₀ : ListBlank Γ) :
    (toCfg x l₀ default) [M]⊢* (toCfg x' l₀ default) := by
  induction n generalizing x with
  | zero =>
    dsimp [steps_r0inf] at h
    rcases hstep : step_r0inf M x with _ | y <;> rw [hstep] at h
    · cases h
      exact stepStar_refl M _
    · cases h
  | succ n ih =>
    dsimp [steps_r0inf] at h
    rcases hstep : step_r0inf M x with _ | y <;> rw [hstep] at h
    · cases h
      exact stepStar_refl M _
    · exact stepStar_trans ⟨1, step_r0inf_spec M x hstep l₀⟩ (ih y h)

theorem steps1_spec_true (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : steps1 M n x = some (x', true)) (l₀ r₀ : ListBlank Γ) :
    (toCfg x l₀ r₀) [M]⊢⁺ (toCfg x' l₀ r₀) := by
  dsimp [steps1] at h
  rcases hstep : step M x with _ | y <;> rw [hstep] at h <;> dsimp only at h
  · cases h
  · rcases hsteps : steps M n y with _ | z <;> rw [hsteps] at h
    · cases h
    · cases h
      exact stepPlus_stepStar_trans ⟨1, by decide, step_spec M x hstep l₀ r₀⟩
        (steps_spec M n y hsteps l₀ r₀)

theorem steps1_spec_star (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ} {flag : Bool}
    (h : steps1 M n x = some (x', flag)) (l₀ r₀ : ListBlank Γ) :
    (toCfg x l₀ r₀) [M]⊢* (toCfg x' l₀ r₀) := by
  dsimp [steps1] at h
  rcases hstep : step M x with _ | y <;> rw [hstep] at h <;> dsimp only at h
  · cases h
    exact stepStar_refl M _
  · rcases hsteps : steps M n y with _ | z <;> rw [hsteps] at h
    · cases h
    · cases h
      exact stepStar_trans ⟨1, step_spec M x hstep l₀ r₀⟩ (steps_spec M n y hsteps l₀ r₀)

theorem steps1_r0inf_spec (M : Machine Γ Λ) (n : ℕ) (x : BCfg Γ Λ) {x' : BCfg Γ Λ}
    (h : steps1_r0inf M n x = some x') (l₀ : ListBlank Γ) :
    (toCfg x l₀ default) [M]⊢⁺ (toCfg x' l₀ default) := by
  dsimp [steps1_r0inf] at h
  rcases hstep : step_r0inf M x with _ | y <;> rw [hstep] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, step_r0inf_spec M x hstep l₀⟩
      (steps_r0inf_spec M n y h l₀)

/-- Strip prefix `r₀` from list `r` if `r₀` is a prefix of `r`. -/
def skipPrefixList (r₀ r : List Γ) : Option (List Γ) :=
  let len := r₀.length
  if r₀ == r.take len then some (r.drop len) else none

theorem skipPrefixList_spec {r₀ r r' : List Γ}
    (h : skipPrefixList r₀ r = some r') :
    r = r₀ ++ r' := by
  dsimp [skipPrefixList] at h
  split_ifs at h with heq
  · cases h
    have heq' : r.take r₀.length = r₀ := (beq_iff_eq.mp heq).symm
    have h_td := List.take_append_drop r₀.length r
    rw [heq'] at h_td
    exact h_td.symm

/-- Check whether every symbol in `a` equals `default`. -/
def all0 : List Γ → Bool
  | [] => true
  | a₀ :: a₁ => (a₀ == default) && all0 a₁

theorem all0_spec {a : List Γ} (h : all0 a = true) :
    a +> (default : ListBlank Γ) = default := by
  induction a with
  | nil => rfl
  | cons a₀ a₁ ih =>
    dsimp [all0] at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, append_cons, ih h.2]
    change ListBlank.cons (default : ListBlank Γ).head (default : ListBlank Γ).tail = default
    exact ListBlank.cons_head_tail default

/-- Check whether `a +> default = b +> default`. -/
def eqAppR0inf : List Γ → List Γ → Bool
  | [], b => all0 b
  | a₀ :: a₁, [] => all0 (a₀ :: a₁)
  | a₀ :: a₁, b₀ :: b₁ => (a₀ == b₀) && eqAppR0inf a₁ b₁

theorem eqAppR0inf_spec {a b : List Γ} (h : eqAppR0inf a b = true) :
    a +> (default : ListBlank Γ) = b +> default := by
  induction a generalizing b with
  | nil => exact (all0_spec h).symm
  | cons a₀ a₁ ih =>
    rcases b with _ | ⟨b₀, b₁⟩
    · exact all0_spec h
    · dsimp [eqAppR0inf] at h
      rw [Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, append_cons, append_cons, ih h.2]

/-- Strip prefix `r₀` from `r +> default`. -/
def skipPrefixListR0inf (r₀ r : List Γ) : Option (List Γ) :=
  let len₀ := r₀.length
  if r₀ == r.take len₀ then
    some (r.drop len₀)
  else
    let len := r.length
    if r == r₀.take len then
      if all0 (r₀.drop len) then some [] else none
    else
      none

theorem skipPrefixListR0inf_spec {r₀ r r' : List Γ}
    (h : skipPrefixListR0inf r₀ r = some r') :
    r +> (default : ListBlank Γ) = r₀ +> (r' +> default) := by
  dsimp [skipPrefixListR0inf] at h
  split_ifs at h with h₁ h₂ h₃
  · cases h
    have heq : r.take r₀.length = r₀ := (beq_iff_eq.mp h₁).symm
    have h_td := List.take_append_drop r₀.length r
    rw [heq] at h_td
    rw [← append_assoc, h_td]
  · cases h
    have heq : r = r₀.take r.length := beq_iff_eq.mp h₂
    have hall : r₀.drop r.length +> (default : ListBlank Γ) = default := all0_spec h₃
    conv_rhs => rw [append_nil, ← List.take_append_drop r.length r₀, append_assoc, hall, ← heq]

mutual

/-- Decidable reflective verifier for `SegRLs M ls₁ ls₂ w₁ w₂` (`BoundedConfig.segRLs_c`). -/
def segRLs_c (M : Machine Γ Λ) (ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ))
    (w₁ w₂ : List Γ) : ℕ → Bool
  | 0 => false
  | T + 1 =>
    match ls₁ with
    | [] => (ls₂ == []) && (w₁ == w₂)
    | ((QR, qR), (QL, qL)) :: ls₁' =>
      match steps1 M T ⟨qR, w₁, QR, .right⟩ with
      | some (⟨l, r, q, .right⟩, _flag) =>
        match ls₂ with
        | [] => false
        | ((QR', qR'), hL') :: ls₂' =>
          (r == []) && (q == QR') &&
          match skipPrefixList qR' l with
          | some w₁' => segLLs_c M (QL, qL) ls₁' hL' ls₂' w₁' w₂ T
          | none => false
      | some (⟨l, r, q, .left⟩, true) =>
        (r == []) && (q == QL) &&
        match skipPrefixList qL l with
        | some w₁' => segRLs_c M ls₁' ls₂ w₁' w₂ T
        | none => false
      | _ => false

/-- Decidable reflective verifier for `SegLLs M h₁ ls₁ h₂ ls₂ w₁ w₂` (`BoundedConfig.segLLs_c`). -/
def segLLs_c (M : Machine Γ Λ) (h₁ : DH0 Γ Λ) (ls₁ : List (DH0 Γ Λ × DH0 Γ Λ))
    (h₂ : DH0 Γ Λ) (ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)) (w₁ w₂ : List Γ) : ℕ → Bool
  | 0 => false
  | T + 1 =>
    let (QL, qL) := h₂
    match steps1 M T ⟨qL, w₁, QL, .left⟩ with
    | some (⟨l, r, q, .right⟩, _flag) =>
      match ls₂ with
      | [] => false
      | ((QR', qR'), hL') :: ls₂' =>
        (r == []) && (q == QR') &&
        match skipPrefixList qR' l with
        | some w₁' => segLLs_c M h₁ ls₁ hL' ls₂' w₁' w₂ T
        | none => false
    | some (⟨l, r, q, .left⟩, _flag) =>
      let (QL₀, qL₀) := h₁
      (r == []) && (q == QL₀) &&
      match skipPrefixList qL₀ l with
      | some w₁' => segRLs_c M ls₁ ls₂ w₁' w₂ T
      | none => false
    | _ => false

end

private theorem segRLs_LLs_c_spec (M : Machine Γ Λ) (T : ℕ) :
    (∀ ls₁ ls₂ w₁ w₂, segRLs_c M ls₁ ls₂ w₁ w₂ T = true → SegRLs M ls₁ ls₂ w₁ w₂) ∧
    (∀ h₁ ls₁ h₂ ls₂ w₁ w₂, segLLs_c M h₁ ls₁ h₂ ls₂ w₁ w₂ T = true →
      SegLLs M h₁ ls₁ h₂ ls₂ w₁ w₂) := by
  induction T with
  | zero =>
    constructor
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ h; cases h
  | succ T ih =>
    rcases ih with ⟨ih_rl, ih_ll⟩
    refine ⟨?_, ?_⟩
    · intro ls₁ ls₂ w₁ w₂ h
      rcases ls₁ with _ | ⟨⟨⟨QR, qR⟩, ⟨QL, qL⟩⟩, ls₁'⟩
      · rw [segRLs_c] at h
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
        rw [h.1, h.2]
        exact .nil w₂
      · rw [segRLs_c] at h
        rcases h_st : steps1 M T ⟨qR, w₁, QR, .right⟩ with _ | ⟨⟨l, r, q, _ | _⟩, _ | _⟩ <;>
          rw [h_st] at h <;> dsimp only at h
        · cases h
        · cases h
        · rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨rfl, rfl, h_skip⟩
          rcases h_sp : skipPrefixList qL l with _ | w₁' <;> rw [h_sp] at h_skip
          · cases h_skip
          · have hl_eq := skipPrefixList_spec h_sp
            refine .cons (fun l₀ r₀ => ?_) (ih_rl ls₁' ls₂ w₁' w₂ h_skip)
            have h_run := steps1_spec_true M T ⟨qR, w₁, QR, .right⟩ h_st l₀ r₀
            simp only [toCfg, toDHCfg, hl_eq, append_nil, append_assoc] at h_run ⊢
            exact h_run
        · rcases ls₂ with _ | ⟨⟨⟨QR', qR'⟩, hL'⟩, ls₂'⟩
          · cases h
          · dsimp only at h
            rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨rfl, rfl, h_skip⟩
            rcases h_sp : skipPrefixList qR' l with _ | w₁' <;> rw [h_sp] at h_skip
            · cases h_skip
            · have hl_eq := skipPrefixList_spec h_sp
              refine SegRLs.of_segRR_segLLs (fun l₀ r₀ => ?_)
                (ih_ll (QL, qL) ls₁' hL' ls₂' w₁' w₂ h_skip)
              have h_run := steps1_spec_star M T ⟨qR, w₁, QR, .right⟩ h_st l₀ r₀
              simp only [toCfg, toDHCfg, hl_eq, append_nil, append_assoc] at h_run ⊢
              exact h_run
        · rcases ls₂ with _ | ⟨⟨⟨QR', qR'⟩, hL'⟩, ls₂'⟩
          · cases h
          · dsimp only at h
            rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨rfl, rfl, h_skip⟩
            rcases h_sp : skipPrefixList qR' l with _ | w₁' <;> rw [h_sp] at h_skip
            · cases h_skip
            · have hl_eq := skipPrefixList_spec h_sp
              refine SegRLs.of_segRR_segLLs (fun l₀ r₀ => ?_)
                (ih_ll (QL, qL) ls₁' hL' ls₂' w₁' w₂ h_skip)
              have h_run := steps1_spec_star M T ⟨qR, w₁, QR, .right⟩ h_st l₀ r₀
              simp only [toCfg, toDHCfg, hl_eq, append_nil, append_assoc] at h_run ⊢
              exact h_run
    · intro h₁ ls₁ h₂ ls₂ w₁ w₂ h
      rcases h₂ with ⟨QL, qL⟩
      rw [segLLs_c] at h
      dsimp only at h
      rcases h_st : steps1 M T ⟨qL, w₁, QL, .left⟩ with _ | ⟨⟨l, r, q, _ | _⟩, flag⟩ <;>
        rw [h_st] at h <;> dsimp only at h
      · cases h
      · rcases h₁ with ⟨QL₀, qL₀⟩
        rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl, h_skip⟩
        rcases h_sp : skipPrefixList qL₀ l with _ | w₁' <;> rw [h_sp] at h_skip
        · cases h_skip
        · have hl_eq := skipPrefixList_spec h_sp
          refine SegLLs.of_segLL_segRLs (fun l₀ r₀ => ?_) (ih_rl ls₁ ls₂ w₁' w₂ h_skip)
          have h_run := steps1_spec_star M T ⟨qL, w₁, QL, .left⟩ h_st l₀ r₀
          simp only [toCfg, toDHCfg, hl_eq, append_nil, append_assoc] at h_run ⊢
          exact h_run
      · rcases ls₂ with _ | ⟨⟨⟨QR', qR'⟩, hL'⟩, ls₂'⟩
        · cases h
        · dsimp only at h
          rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨rfl, rfl, h_skip⟩
          rcases h_sp : skipPrefixList qR' l with _ | w₁' <;> rw [h_sp] at h_skip
          · cases h_skip
          · have hl_eq := skipPrefixList_spec h_sp
            refine SegLLs.of_segLR_segLLs (fun l₀ r₀ => ?_)
              (ih_ll h₁ ls₁ hL' ls₂' w₁' w₂ h_skip)
            have h_run := steps1_spec_star M T ⟨qL, w₁, QL, .left⟩ h_st l₀ r₀
            simp only [toCfg, toDHCfg, hl_eq, append_nil, append_assoc] at h_run ⊢
            exact h_run

/-- Soundness of the reflective 2D tile checker (`BoundedConfig.segRLs_c_spec`): any tile check
that evaluates to `true` by `rfl` or `decide` yields `SegRLs M ls₁ ls₂ w₁ w₂`. -/
theorem segRLs_c_spec (M : Machine Γ Λ) {ls₁ ls₂ : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₂ : List Γ} {T : ℕ}
    (h : segRLs_c M ls₁ ls₂ w₁ w₂ T = true) :
    SegRLs M ls₁ ls₂ w₁ w₂ :=
  (segRLs_LLs_c_spec M T).1 ls₁ ls₂ w₁ w₂ h

/-- Decidable reflective verifier for `SideRLs M hs (r +> default) (r' +> default)`
(`BoundedConfig.sideRLs_c`). -/
def sideRLs_c (M : Machine Γ Λ) :
    List (DH0 Γ Λ × DH0 Γ Λ) → List Γ → List Γ → ℕ → Bool
  | [], r, r', _ => eqAppR0inf r r'
  | ((QR, qR), (QL, qL)) :: hs, r, r', T =>
    match steps1_r0inf M T ⟨qR, r, QR, .right⟩ with
    | some ⟨l, r_rem, QL', .left⟩ =>
      (r_rem == []) && (QL == QL') &&
      match skipPrefixListR0inf qL l with
      | some r₀ => sideRLs_c M hs r₀ r' T
      | none => false
    | _ => false

/-- Soundness of the reflective half-tape checker (`BoundedConfig.sideRLs_c_spec`). -/
theorem sideRLs_c_spec (M : Machine Γ Λ) {hs : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r r' : List Γ} {T : ℕ}
    (h : sideRLs_c M hs r r' T = true) :
    SideRLs M hs (r +> default) (r' +> default) := by
  induction hs generalizing r with
  | nil =>
    rw [eqAppR0inf_spec h]
    exact .nil _
  | cons ab hs ih =>
    rcases ab with ⟨⟨QR, qR⟩, ⟨QL, qL⟩⟩
    dsimp [sideRLs_c] at h
    rcases h_st : steps1_r0inf M T ⟨qR, r, QR, .right⟩ with _ | ⟨l, r_rem, QL', _ | _⟩ <;>
      rw [h_st] at h <;> dsimp only at h
    · cases h
    · rw [Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, rfl, h_skip⟩
      rcases h_sp : skipPrefixListR0inf qL l with _ | r₀ <;> rw [h_sp] at h_skip
      · cases h_skip
      · have hl_eq := skipPrefixListR0inf_spec h_sp
        refine .cons (fun l₀ => ?_) (ih h_skip)
        have h_run := steps1_r0inf_spec M T ⟨qR, r, QR, .right⟩ h_st l₀
        simp only [toCfg, toDHCfg, hl_eq, append_nil] at h_run ⊢
        exact h_run
    · cases h

end Decidable

end BoundedConfig

section NatSim

open Turing BusyBeaver

private lemma multiStep_of_step {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {M : Machine Γ Λ} {c c' : Cfg Γ Λ}
    (h : step M c = some c') (n : ℕ) :
    multiStep M c (n + 1) = multiStep M c' n := by
  rw [multiStep_succ', h, Option.bind_some]

/-- Strict evaluation barrier for `Nat` terms inside Lean's call-by-name kernel.

Because Lean's kernel uses weak-head reduction, evaluating recursive tape updates in `stepsNat`
without forcing eager evaluation would accumulate unreduced thunk trees `w + 2 * (w' + 2 * ...)`
for the tape integers `l` and `r`, leading to quadratic memory blowup and elaborator/kernel stack
overflow over thousands of steps.

Pattern matching on `Nat.add n 1` forces the kernel's native C++ bignum evaluator (`reduce_nat` via `lean::mpz`)
to eagerly compute the normal form of `n` before continuing, acting as a kernel-level `seq`.
Mathematically, `withReducedNat n k = k n` by definition (`rfl`). -/
def withReducedNat {α : Type*} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (Nat.add n 1) (k 0) (fun m => k m)

@[simp] theorem withReducedNat_eq {α : Type*} (n : Nat) (k : Nat → α) :
    withReducedNat n k = k n := rfl

/-- Decode a binary Nat (head = n % 2, tail = n / 2) into a canonical ListBlank (Fin 2). -/
def decodeHalf (n : Nat) : ListBlank (Fin 2) :=
  if n = 0 then default
  else ListBlank.cons ⟨n % 2, Nat.mod_lt _ (by decide)⟩ (decodeHalf (n / 2))
termination_by n

@[simp] theorem decodeHalf_zero : decodeHalf 0 = default := by
  unfold decodeHalf; rfl

theorem decodeHalf_unfold (n : Nat) :
    decodeHalf n = ListBlank.cons ⟨n % 2, Nat.mod_lt _ (by decide)⟩ (decodeHalf (n / 2)) := by
  rw [decodeHalf]
  split_ifs with h
  · subst h
    rw [decodeHalf_zero]
    have hhead : (⟨0 % 2, Nat.mod_lt 0 (by decide)⟩ : Fin 2) = default := rfl
    rw [hhead]
    exact (ListBlank.cons_head_tail default).symm
  · rfl

@[simp] theorem decodeHalf_head (n : Nat) :
    (decodeHalf n).head = ⟨n % 2, Nat.mod_lt _ (by decide)⟩ := by
  rw [decodeHalf_unfold, ListBlank.head_cons]

@[simp] theorem decodeHalf_tail (n : Nat) :
    (decodeHalf n).tail = decodeHalf (n / 2) := by
  rw [decodeHalf_unfold, ListBlank.tail_cons]

@[simp] theorem decodeHalf_cons (b : Fin 2) (n : Nat) :
    ListBlank.cons b (decodeHalf n) = decodeHalf (b.val + 2 * n) := by
  rw [decodeHalf_unfold (b.val + 2 * n)]
  have hm : (b.val + 2 * n) % 2 = b.val := by omega
  have hd : (b.val + 2 * n) / 2 = n := by omega
  congr 1
  · exact Fin.ext hm.symm
  · rw [hd]

def encodeList (xs : List (Fin 2)) (rest : Nat := 0) : Nat :=
  xs.foldr (fun b acc => b.val + 2 * acc) rest

@[simp] theorem decodeHalf_encodeList (xs : List (Fin 2)) (rest : Nat) :
    ListBlank.append xs (decodeHalf rest) = decodeHalf (encodeList xs rest) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change ListBlank.cons b (ListBlank.append xs (decodeHalf rest)) = _
    rw [ih, decodeHalf_cons]
    rfl

/-- Native bignum 4-Nat shadow configuration for any Machine (Fin 2) (Fin K).
    q < K is an active state, q = K is none (halted), and q = K + 1 flags an invalid step. -/
structure NatCfg where
  q : Nat
  h : Nat
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def NatCfg.toCfg {K : Nat} [NeZero K] (c : NatCfg) : Cfg (Fin 2) (Fin K) :=
  ⟨if hq : c.q < K then some ⟨c.q, hq⟩ else none,
   ⟨⟨c.h % 2, Nat.mod_lt _ (by decide)⟩, decodeHalf c.l, decodeHalf c.r⟩⟩

/-- Run n strict bignum shadow steps for arbitrary M : Machine (Fin 2) (Fin K). -/
def stepsNat {K : Nat} [NeZero K] (M : Machine (Fin 2) (Fin K)) : Nat → NatCfg → NatCfg
  | 0, c => c
  | n + 1, c =>
    if hq : c.q < K then
      match M ⟨c.q, hq⟩ ⟨c.h % 2, Nat.mod_lt _ (by decide)⟩ with
      | none => ⟨K + 1, 0, 0, 0⟩
      | some (oq', Stmt.write w d) =>
        let q' := match oq' with | some s => s.val | none => K
        match d with
        | .right =>
          withReducedNat (c.r % 2) fun h' =>
          withReducedNat (c.r / 2) fun r' =>
          withReducedNat (w.val + 2 * c.l) fun l' =>
          stepsNat M n ⟨q', h', l', r'⟩
        | .left =>
          withReducedNat (c.l % 2) fun h' =>
          withReducedNat (c.l / 2) fun l' =>
          withReducedNat (w.val + 2 * c.r) fun r' =>
          stepsNat M n ⟨q', h', l', r'⟩
    else
      ⟨K + 1, 0, 0, 0⟩

theorem stepsNat_sound {K : Nat} [NeZero K] (M : Machine (Fin 2) (Fin K)) :
    ∀ (n : Nat) (c c' : NatCfg),
      stepsNat M n c = c' → c'.q ≤ K →
      multiStep M (c.toCfg (K := K)) n = some (c'.toCfg (K := K))
  | 0, c, c', heq, _ => by subst heq; rfl
  | n + 1, c, c', heq, hle => by
    dsimp [stepsNat] at heq
    split_ifs at heq with hq
    · rcases hM : M ⟨c.q, hq⟩ ⟨c.h % 2, Nat.mod_lt _ (by decide)⟩ with _ | ⟨oq', ⟨w, d⟩⟩
      · rw [hM] at heq
        subst heq
        dsimp only at hle
        omega
      · rw [hM] at heq
        rcases oq' with _ | s <;> rcases d with _ | _
        · have hstep : step M (c.toCfg (K := K)) =
            some (NatCfg.toCfg (K := K) ⟨K, c.l % 2, c.l / 2, w.val + 2 * c.r⟩) := by
            simp [BusyBeaver.step, NatCfg.toCfg, hq, hM, Tape.write, Tape.move]
          rw [multiStep_of_step hstep]; exact stepsNat_sound M n _ c' heq hle
        · have hstep : step M (c.toCfg (K := K)) =
            some (NatCfg.toCfg (K := K) ⟨K, c.r % 2, w.val + 2 * c.l, c.r / 2⟩) := by
            simp [BusyBeaver.step, NatCfg.toCfg, hq, hM, Tape.write, Tape.move]
          rw [multiStep_of_step hstep]; exact stepsNat_sound M n _ c' heq hle
        · have hstep : step M (c.toCfg (K := K)) =
            some (NatCfg.toCfg (K := K) ⟨s.val, c.l % 2, c.l / 2, w.val + 2 * c.r⟩) := by
            simp [BusyBeaver.step, NatCfg.toCfg, hq, hM, Tape.write, Tape.move, s.isLt]
          rw [multiStep_of_step hstep]; exact stepsNat_sound M n _ c' heq hle
        · have hstep : step M (c.toCfg (K := K)) =
            some (NatCfg.toCfg (K := K) ⟨s.val, c.r % 2, w.val + 2 * c.l, c.r / 2⟩) := by
            simp [BusyBeaver.step, NatCfg.toCfg, hq, hM, Tape.write, Tape.move, s.isLt]
          rw [multiStep_of_step hstep]; exact stepsNat_sound M n _ c' heq hle
    · subst heq
      dsimp only at hle
      omega

theorem toCfg_zero {K : Nat} [NeZero K] :
    (NatCfg.toCfg (K := K) ⟨0, 0, 0, 0⟩) = init [] := by
  have h0 : 0 < K := by
    have := NeZero.ne K
    omega
  ext
  · simp [NatCfg.toCfg, BusyBeaver.init, h0]
    try rfl
  · simp [NatCfg.toCfg, BusyBeaver.init, Tape.mk₁, decodeHalf_zero]
    try rfl

theorem toCfg_headRight {K : Nat} [NeZero K] (q : Fin K) (l r : Nat) :
    NatCfg.toCfg (K := K) ⟨q.val, r % 2, l, r / 2⟩ =
    Cfg.headRight q (decodeHalf l) (decodeHalf r) := by
  ext <;> simp [NatCfg.toCfg, Cfg.headRight, q.isLt]

theorem toCfg_headLeft {K : Nat} [NeZero K] (q : Fin K) (l r : Nat) :
    NatCfg.toCfg (K := K) ⟨q.val, l % 2, l / 2, r⟩ =
    Cfg.headLeft q (decodeHalf l) (decodeHalf r) := by
  ext <;> simp [NatCfg.toCfg, Cfg.headLeft, q.isLt]

end NatSim

end BusyBeaver.Longitudinal
