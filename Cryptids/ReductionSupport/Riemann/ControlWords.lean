/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Cryptids.Riemann104

@[expose] public section
namespace ConjectureMachines.Riemann104.PhaseB1

open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

inductive Instr where
  | halt
  | jump (s : Fin 121)
  | inc (r : Fin 5) (s : Fin 121)
  | decnz (r : Fin 5) (s f : Fin 121)
  deriving DecidableEq

def stack (s : Fin 121) : List (Fin 2) :=
  match s.val with
  | 0 => []
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | 3 => [1]
  | 4 => [1, 0, 0, 1]
  | 5 => [1, 0, 0, 1, 0, 0, 1]
  | 6 => [1, 0, 0, 1, 0, 0, 1, 1]
  | 7 => [1, 0, 0, 1, 0, 1]
  | 8 => [1, 0, 0, 1, 0, 1, 0, 1]
  | 9 => [1, 0, 0, 1, 0, 1, 0, 1, 1]
  | 10 => [1, 0, 0, 1, 0, 1, 1]
  | 11 => [1, 0, 0, 1, 0, 1, 1, 1]
  | 12 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1]
  | 13 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1]
  | 14 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 1]
  | 15 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1]
  | 16 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1]
  | 17 => [1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1]
  | 18 => [1, 0, 0, 1, 0, 1, 1, 1, 1]
  | 19 => [1, 0, 0, 1, 1]
  | 20 => [1, 0, 0, 1, 1, 0, 1]
  | 21 => [1, 0, 0, 1, 1, 0, 1, 1]
  | 22 => [1, 0, 0, 1, 1, 0, 1, 1, 0, 1]
  | 23 => [1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  | 24 => [1, 0, 0, 1, 1, 0, 1, 1, 1]
  | 25 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1]
  | 26 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
  | 27 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1]
  | 28 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1]
  | 29 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1]
  | 30 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]
  | 31 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 1]
  | 32 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1]
  | 33 => [1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1]
  | 34 => [1, 0, 0, 1, 1, 1]
  | 35 => [1, 0, 0, 1, 1, 1, 0, 0, 1]
  | 36 => [1, 0, 0, 1, 1, 1, 0, 0, 1, 1]
  | 37 => [1, 0, 0, 1, 1, 1, 0, 1]
  | 38 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1]
  | 39 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1]
  | 40 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
  | 41 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 1]
  | 42 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1]
  | 43 => [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]
  | 44 => [1, 0, 0, 1, 1, 1, 0, 1, 1]
  | 45 => [1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
  | 46 => [1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1]
  | 47 => [1, 0, 0, 1, 1, 1, 1]
  | 48 => [1, 0, 0, 1, 1, 1, 1, 0, 1]
  | 49 => [1, 0, 0, 1, 1, 1, 1, 0, 1, 1]
  | 50 => [1, 0, 0, 1, 1, 1, 1, 1]
  | 51 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1]
  | 52 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1]
  | 53 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
  | 54 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
  | 55 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1]
  | 56 => [1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1]
  | 57 => [1, 0, 0, 1, 1, 1, 1, 1, 1]
  | 58 => [1, 0, 0, 1, 1, 1, 1, 1, 1, 1]
  | 59 => [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
  | 60 => [1, 0, 1]
  | 61 => [1, 0, 1, 1]
  | 62 => [1, 1]
  | 63 => [1, 1, 0, 1]
  | 64 => [1, 1, 0, 1, 0, 1]
  | 65 => [1, 1, 0, 1, 1]
  | 66 => [1, 1, 1]
  | 67 => [1, 1, 1, 0, 0, 1]
  | 68 => [1, 1, 1, 0, 0, 1, 0, 0, 1]
  | 69 => [1, 1, 1, 0, 0, 1, 0, 0, 1, 1]
  | 70 => [1, 1, 1, 0, 0, 1, 0, 1]
  | 71 => [1, 1, 1, 0, 0, 1, 0, 1, 0, 1]
  | 72 => [1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]
  | 73 => [1, 1, 1, 0, 0, 1, 0, 1, 1]
  | 74 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1]
  | 75 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1]
  | 76 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1]
  | 77 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1]
  | 78 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1]
  | 79 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1]
  | 80 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1]
  | 81 => [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1]
  | 82 => [1, 1, 1, 0, 0, 1, 1]
  | 83 => [1, 1, 1, 0, 0, 1, 1, 0, 1]
  | 84 => [1, 1, 1, 0, 0, 1, 1, 1]
  | 85 => [1, 1, 1, 0, 1]
  | 86 => [1, 1, 1, 0, 1, 1]
  | 87 => [1, 1, 1, 0, 1, 1, 1]
  | 88 => [1, 1, 1, 1]
  | 89 => [1, 1, 1, 1, 0, 1]
  | 90 => [1, 1, 1, 1, 0, 1, 0, 1]
  | 91 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1]
  | 92 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
  | 93 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1]
  | 94 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
  | 95 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1]
  | 96 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1]
  | 97 => [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1]
  | 98 => [1, 1, 1, 1, 0, 1, 0, 1, 1]
  | 99 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
  | 100 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1]
  | 101 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1]
  | 102 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
  | 103 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | 104 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]
  | 105 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1]
  | 106 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1]
  | 107 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]
  | 108 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1]
  | 109 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1]
  | 110 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
  | 111 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1]
  | 112 => [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
  | 113 => [1, 1, 1, 1, 0, 1, 1]
  | 114 => [1, 1, 1, 1, 0, 1, 1, 1]
  | 115 => [1, 1, 1, 1, 1]
  | 116 => [1, 1, 1, 1, 1, 0, 1]
  | 117 => [1, 1, 1, 1, 1, 0, 1, 0, 1]
  | 118 => [1, 1, 1, 1, 1, 0, 1, 1]
  | 119 => [1, 1, 1, 1, 1, 1]
  | 120 => [1, 1, 1, 1, 1, 1, 1]
  | _ => []

def instr (s : Fin 121) : Instr :=
  match s.val with
  | 0 => .decnz ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩
  | 1 => .inc ⟨3, by decide⟩ ⟨2, by decide⟩
  | 2 => .jump ⟨0, by decide⟩
  | 3 => .inc ⟨1, by decide⟩ ⟨4, by decide⟩
  | 4 => .decnz ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨7, by decide⟩
  | 5 => .inc ⟨4, by decide⟩ ⟨6, by decide⟩
  | 6 => .jump ⟨4, by decide⟩
  | 7 => .decnz ⟨2, by decide⟩ ⟨8, by decide⟩ ⟨10, by decide⟩
  | 8 => .inc ⟨0, by decide⟩ ⟨9, by decide⟩
  | 9 => .jump ⟨7, by decide⟩
  | 10 => .decnz ⟨0, by decide⟩ ⟨11, by decide⟩ ⟨19, by decide⟩
  | 11 => .decnz ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨14, by decide⟩
  | 12 => .inc ⟨1, by decide⟩ ⟨13, by decide⟩
  | 13 => .jump ⟨18, by decide⟩
  | 14 => .decnz ⟨1, by decide⟩ ⟨15, by decide⟩ ⟨17, by decide⟩
  | 15 => .inc ⟨4, by decide⟩ ⟨16, by decide⟩
  | 16 => .jump ⟨14, by decide⟩
  | 17 => .inc ⟨2, by decide⟩ ⟨18, by decide⟩
  | 18 => .jump ⟨10, by decide⟩
  | 19 => .decnz ⟨4, by decide⟩ ⟨20, by decide⟩ ⟨34, by decide⟩
  | 20 => .inc ⟨4, by decide⟩ ⟨21, by decide⟩
  | 21 => .decnz ⟨2, by decide⟩ ⟨22, by decide⟩ ⟨24, by decide⟩
  | 22 => .inc ⟨0, by decide⟩ ⟨23, by decide⟩
  | 23 => .jump ⟨21, by decide⟩
  | 24 => .decnz ⟨1, by decide⟩ ⟨25, by decide⟩ ⟨28, by decide⟩
  | 25 => .inc ⟨4, by decide⟩ ⟨26, by decide⟩
  | 26 => .inc ⟨2, by decide⟩ ⟨27, by decide⟩
  | 27 => .jump ⟨24, by decide⟩
  | 28 => .decnz ⟨4, by decide⟩ ⟨29, by decide⟩ ⟨31, by decide⟩
  | 29 => .inc ⟨1, by decide⟩ ⟨30, by decide⟩
  | 30 => .jump ⟨28, by decide⟩
  | 31 => .decnz ⟨0, by decide⟩ ⟨32, by decide⟩ ⟨34, by decide⟩
  | 32 => .inc ⟨2, by decide⟩ ⟨33, by decide⟩
  | 33 => .jump ⟨24, by decide⟩
  | 34 => .decnz ⟨2, by decide⟩ ⟨35, by decide⟩ ⟨37, by decide⟩
  | 35 => .inc ⟨0, by decide⟩ ⟨36, by decide⟩
  | 36 => .jump ⟨34, by decide⟩
  | 37 => .decnz ⟨1, by decide⟩ ⟨38, by decide⟩ ⟨41, by decide⟩
  | 38 => .inc ⟨4, by decide⟩ ⟨39, by decide⟩
  | 39 => .inc ⟨2, by decide⟩ ⟨40, by decide⟩
  | 40 => .jump ⟨37, by decide⟩
  | 41 => .decnz ⟨4, by decide⟩ ⟨42, by decide⟩ ⟨44, by decide⟩
  | 42 => .inc ⟨1, by decide⟩ ⟨43, by decide⟩
  | 43 => .jump ⟨41, by decide⟩
  | 44 => .decnz ⟨0, by decide⟩ ⟨45, by decide⟩ ⟨47, by decide⟩
  | 45 => .inc ⟨2, by decide⟩ ⟨46, by decide⟩
  | 46 => .jump ⟨37, by decide⟩
  | 47 => .decnz ⟨2, by decide⟩ ⟨48, by decide⟩ ⟨50, by decide⟩
  | 48 => .inc ⟨0, by decide⟩ ⟨49, by decide⟩
  | 49 => .jump ⟨47, by decide⟩
  | 50 => .decnz ⟨1, by decide⟩ ⟨51, by decide⟩ ⟨54, by decide⟩
  | 51 => .inc ⟨4, by decide⟩ ⟨52, by decide⟩
  | 52 => .inc ⟨2, by decide⟩ ⟨53, by decide⟩
  | 53 => .jump ⟨50, by decide⟩
  | 54 => .decnz ⟨4, by decide⟩ ⟨55, by decide⟩ ⟨57, by decide⟩
  | 55 => .inc ⟨1, by decide⟩ ⟨56, by decide⟩
  | 56 => .jump ⟨54, by decide⟩
  | 57 => .decnz ⟨0, by decide⟩ ⟨58, by decide⟩ ⟨60, by decide⟩
  | 58 => .inc ⟨2, by decide⟩ ⟨59, by decide⟩
  | 59 => .jump ⟨50, by decide⟩
  | 60 => .decnz ⟨3, by decide⟩ ⟨61, by decide⟩ ⟨62, by decide⟩
  | 61 => .jump ⟨3, by decide⟩
  | 62 => .decnz ⟨1, by decide⟩ ⟨63, by decide⟩ ⟨66, by decide⟩
  | 63 => .inc ⟨4, by decide⟩ ⟨64, by decide⟩
  | 64 => .inc ⟨3, by decide⟩ ⟨65, by decide⟩
  | 65 => .jump ⟨62, by decide⟩
  | 66 => .decnz ⟨2, by decide⟩ ⟨67, by decide⟩ ⟨85, by decide⟩
  | 67 => .decnz ⟨1, by decide⟩ ⟨68, by decide⟩ ⟨70, by decide⟩
  | 68 => .inc ⟨4, by decide⟩ ⟨69, by decide⟩
  | 69 => .jump ⟨67, by decide⟩
  | 70 => .decnz ⟨2, by decide⟩ ⟨71, by decide⟩ ⟨73, by decide⟩
  | 71 => .inc ⟨0, by decide⟩ ⟨72, by decide⟩
  | 72 => .jump ⟨70, by decide⟩
  | 73 => .decnz ⟨0, by decide⟩ ⟨74, by decide⟩ ⟨82, by decide⟩
  | 74 => .decnz ⟨4, by decide⟩ ⟨75, by decide⟩ ⟨77, by decide⟩
  | 75 => .inc ⟨1, by decide⟩ ⟨76, by decide⟩
  | 76 => .jump ⟨81, by decide⟩
  | 77 => .decnz ⟨1, by decide⟩ ⟨78, by decide⟩ ⟨80, by decide⟩
  | 78 => .inc ⟨4, by decide⟩ ⟨79, by decide⟩
  | 79 => .jump ⟨77, by decide⟩
  | 80 => .inc ⟨2, by decide⟩ ⟨81, by decide⟩
  | 81 => .jump ⟨73, by decide⟩
  | 82 => .decnz ⟨3, by decide⟩ ⟨83, by decide⟩ ⟨84, by decide⟩
  | 83 => .jump ⟨84, by decide⟩
  | 84 => .jump ⟨66, by decide⟩
  | 85 => .decnz ⟨4, by decide⟩ ⟨86, by decide⟩ ⟨88, by decide⟩
  | 86 => .inc ⟨1, by decide⟩ ⟨87, by decide⟩
  | 87 => .jump ⟨85, by decide⟩
  | 88 => .decnz ⟨1, by decide⟩ ⟨89, by decide⟩ ⟨115, by decide⟩
  | 89 => .inc ⟨0, by decide⟩ ⟨90, by decide⟩
  | 90 => .decnz ⟨1, by decide⟩ ⟨91, by decide⟩ ⟨95, by decide⟩
  | 91 => .inc ⟨0, by decide⟩ ⟨92, by decide⟩
  | 92 => .decnz ⟨1, by decide⟩ ⟨93, by decide⟩ ⟨94, by decide⟩
  | 93 => .inc ⟨4, by decide⟩ ⟨94, by decide⟩
  | 94 => .jump ⟨90, by decide⟩
  | 95 => .decnz ⟨4, by decide⟩ ⟨96, by decide⟩ ⟨98, by decide⟩
  | 96 => .inc ⟨1, by decide⟩ ⟨97, by decide⟩
  | 97 => .jump ⟨95, by decide⟩
  | 98 => .decnz ⟨1, by decide⟩ ⟨99, by decide⟩ ⟨103, by decide⟩
  | 99 => .inc ⟨0, by decide⟩ ⟨100, by decide⟩
  | 100 => .decnz ⟨1, by decide⟩ ⟨101, by decide⟩ ⟨102, by decide⟩
  | 101 => .inc ⟨4, by decide⟩ ⟨102, by decide⟩
  | 102 => .jump ⟨98, by decide⟩
  | 103 => .decnz ⟨4, by decide⟩ ⟨104, by decide⟩ ⟨106, by decide⟩
  | 104 => .inc ⟨1, by decide⟩ ⟨105, by decide⟩
  | 105 => .jump ⟨103, by decide⟩
  | 106 => .decnz ⟨3, by decide⟩ ⟨107, by decide⟩ ⟨110, by decide⟩
  | 107 => .decnz ⟨3, by decide⟩ ⟨108, by decide⟩ ⟨109, by decide⟩
  | 108 => .inc ⟨4, by decide⟩ ⟨109, by decide⟩
  | 109 => .jump ⟨106, by decide⟩
  | 110 => .decnz ⟨4, by decide⟩ ⟨111, by decide⟩ ⟨113, by decide⟩
  | 111 => .inc ⟨3, by decide⟩ ⟨112, by decide⟩
  | 112 => .jump ⟨110, by decide⟩
  | 113 => .inc ⟨2, by decide⟩ ⟨114, by decide⟩
  | 114 => .jump ⟨88, by decide⟩
  | 115 => .decnz ⟨2, by decide⟩ ⟨116, by decide⟩ ⟨119, by decide⟩
  | 116 => .decnz ⟨3, by decide⟩ ⟨117, by decide⟩ ⟨118, by decide⟩
  | 117 => .jump ⟨118, by decide⟩
  | 118 => .jump ⟨88, by decide⟩
  | 119 => .decnz ⟨3, by decide⟩ ⟨120, by decide⟩ ⟨0, by decide⟩
  | 120 => .halt
  | _ => .halt

def allowedBits (s : Fin 121) : Nat :=
  match s.val with
  | 0 => 771
  | 1 => 771
  | 2 => 768
  | 3 => 16705
  | 4 => 1431651396
  | 5 => 1431655765
  | 6 => 1431633920
  | 7 => 858980352
  | 8 => 858980352
  | 9 => 572653568
  | 10 => 4294954188
  | 11 => 4294954188
  | 12 => 4294967295
  | 13 => 3435973836
  | 14 => 4294954188
  | 15 => 4294967295
  | 16 => 4294901760
  | 17 => 858980352
  | 18 => 4244425932
  | 19 => 1431651396
  | 20 => 1431655765
  | 21 => 4294901760
  | 22 => 4294901760
  | 23 => 2863267840
  | 24 => 4294951104
  | 25 => 4294963440
  | 26 => 4294901760
  | 27 => 4042260480
  | 28 => 4294954188
  | 29 => 4294967295
  | 30 => 3435973836
  | 31 => 52428
  | 32 => 52428
  | 33 => 49344
  | 34 => 52428
  | 35 => 52428
  | 36 => 34952
  | 37 => 4042312908
  | 38 => 4042326015
  | 39 => 4294901760
  | 40 => 4042260480
  | 41 => 4042309824
  | 42 => 4042322160
  | 43 => 3233857728
  | 44 => 49344
  | 45 => 49344
  | 46 => 49344
  | 47 => 51400
  | 48 => 52428
  | 49 => 34952
  | 50 => 4042311880
  | 51 => 4042324730
  | 52 => 4210688000
  | 53 => 4042260480
  | 54 => 4042309824
  | 55 => 4042322160
  | 56 => 3233857728
  | 57 => 49344
  | 58 => 49344
  | 59 => 49344
  | 60 => 16448
  | 61 => 16448
  | 62 => 1342177344
  | 63 => 1342177360
  | 64 => 1347420160
  | 65 => 1342177280
  | 66 => 1431651396
  | 67 => 1431651396
  | 68 => 1431655765
  | 69 => 1431633920
  | 70 => 858980352
  | 71 => 858980352
  | 72 => 572653568
  | 73 => 4294954188
  | 74 => 4294954188
  | 75 => 4294967295
  | 76 => 3435973836
  | 77 => 4294954188
  | 78 => 4294967295
  | 79 => 4294901760
  | 80 => 858980352
  | 81 => 4244425932
  | 82 => 1431651396
  | 83 => 1431651396
  | 84 => 1431651396
  | 85 => 84214788
  | 86 => 84215045
  | 87 => 67372036
  | 88 => 42662
  | 89 => 42405
  | 90 => 2863311530
  | 91 => 2863311530
  | 92 => 2863311530
  | 93 => 2863311530
  | 94 => 2863276578
  | 95 => 2863311530
  | 96 => 2863311530
  | 97 => 2290649224
  | 98 => 2863311530
  | 99 => 2863311530
  | 100 => 2863311530
  | 101 => 2863311530
  | 102 => 2863276578
  | 103 => 2863311530
  | 104 => 2863311530
  | 105 => 2290649224
  | 106 => 2863311530
  | 107 => 2863311530
  | 108 => 2863311530
  | 109 => 2863268010
  | 110 => 2863311530
  | 111 => 2863311530
  | 112 => 2852170240
  | 113 => 43690
  | 114 => 41120
  | 115 => 8738
  | 116 => 8738
  | 117 => 8738
  | 118 => 8738
  | 119 => 514
  | 120 => 514
  | _ => 0

def expand : Instr → RhInstr
  | .halt => .halt
  | .jump s => .jump (stack s)
  | .inc r s => .inc r.val (stack s)
  | .decnz r s f => .decnz r.val (stack s) (stack f)

def decode (m : Fin 32) : List Nat :=
  [m.val % 2, (m.val / 2) % 2, (m.val / 4) % 2,
    (m.val / 8) % 2, (m.val / 16) % 2]

def setMask (m : Fin 32) (r : Fin 5) (v : Fin 2) : Fin 32 :=
  ⟨(m.val - ((m.val / 2^r.val) % 2) * 2^r.val + v.val * 2^r.val) % 32,
    Nat.mod_lt _ (by decide)⟩

def allowed (s : Fin 121) (m : Fin 32) : Bool :=
  (allowedBits s / 2^m.val) % 2 == 1

def closedCheck (s : Fin 121) (m : Fin 32) : Prop :=
  allowed s m = true →
  match instr s with
  | .halt => True
  | .jump t => allowed t m = true
  | .inc r t => allowed t (setMask m r 1) = true
  | .decnz r t f =>
    if (decode m).getD r.val 0 = 0 then allowed f m = true
    else allowed t (setMask m r 0) = true ∧ allowed t (setMask m r 1) = true

instance (s : Fin 121) (m : Fin 32) : Decidable (closedCheck s m) := by
  unfold closedCheck
  cases instr s <;> infer_instance

theorem decode_set : ∀ (m : Fin 32) (r : Fin 5) (v : Fin 2),
    decode (setMask m r v) = (decode m).set r.val v.val := by decide

theorem initial_allowed : stack 0 = [] ∧ decode 0 = [0, 0, 0, 0, 0] ∧
    allowed 0 0 = true := by decide

theorem instruction_0 : evalStackOf true (stack 0) = expand (instr 0) := by decide
theorem closed_0 : ∀ m : Fin 32, closedCheck 0 m := by decide

theorem instruction_1 : evalStackOf true (stack 1) = expand (instr 1) := by decide
theorem closed_1 : ∀ m : Fin 32, closedCheck 1 m := by decide

theorem instruction_2 : evalStackOf true (stack 2) = expand (instr 2) := by decide
theorem closed_2 : ∀ m : Fin 32, closedCheck 2 m := by decide

theorem instruction_3 : evalStackOf true (stack 3) = expand (instr 3) := by decide
theorem closed_3 : ∀ m : Fin 32, closedCheck 3 m := by decide

theorem instruction_4 : evalStackOf true (stack 4) = expand (instr 4) := by decide
theorem closed_4 : ∀ m : Fin 32, closedCheck 4 m := by decide

theorem instruction_5 : evalStackOf true (stack 5) = expand (instr 5) := by decide
theorem closed_5 : ∀ m : Fin 32, closedCheck 5 m := by decide

theorem instruction_6 : evalStackOf true (stack 6) = expand (instr 6) := by decide
theorem closed_6 : ∀ m : Fin 32, closedCheck 6 m := by decide

theorem instruction_7 : evalStackOf true (stack 7) = expand (instr 7) := by decide
theorem closed_7 : ∀ m : Fin 32, closedCheck 7 m := by decide

theorem instruction_8 : evalStackOf true (stack 8) = expand (instr 8) := by decide
theorem closed_8 : ∀ m : Fin 32, closedCheck 8 m := by decide

theorem instruction_9 : evalStackOf true (stack 9) = expand (instr 9) := by decide
theorem closed_9 : ∀ m : Fin 32, closedCheck 9 m := by decide

theorem instruction_10 : evalStackOf true (stack 10) = expand (instr 10) := by decide
theorem closed_10 : ∀ m : Fin 32, closedCheck 10 m := by decide

theorem instruction_11 : evalStackOf true (stack 11) = expand (instr 11) := by decide
theorem closed_11 : ∀ m : Fin 32, closedCheck 11 m := by decide

theorem instruction_12 : evalStackOf true (stack 12) = expand (instr 12) := by decide
theorem closed_12 : ∀ m : Fin 32, closedCheck 12 m := by decide

theorem instruction_13 : evalStackOf true (stack 13) = expand (instr 13) := by decide
theorem closed_13 : ∀ m : Fin 32, closedCheck 13 m := by decide

theorem instruction_14 : evalStackOf true (stack 14) = expand (instr 14) := by decide
theorem closed_14 : ∀ m : Fin 32, closedCheck 14 m := by decide

theorem instruction_15 : evalStackOf true (stack 15) = expand (instr 15) := by decide
theorem closed_15 : ∀ m : Fin 32, closedCheck 15 m := by decide

theorem instruction_16 : evalStackOf true (stack 16) = expand (instr 16) := by decide
theorem closed_16 : ∀ m : Fin 32, closedCheck 16 m := by decide

theorem instruction_17 : evalStackOf true (stack 17) = expand (instr 17) := by decide
theorem closed_17 : ∀ m : Fin 32, closedCheck 17 m := by decide

theorem instruction_18 : evalStackOf true (stack 18) = expand (instr 18) := by decide
theorem closed_18 : ∀ m : Fin 32, closedCheck 18 m := by decide

theorem instruction_19 : evalStackOf true (stack 19) = expand (instr 19) := by decide
theorem closed_19 : ∀ m : Fin 32, closedCheck 19 m := by decide

theorem instruction_20 : evalStackOf true (stack 20) = expand (instr 20) := by decide
theorem closed_20 : ∀ m : Fin 32, closedCheck 20 m := by decide

theorem instruction_21 : evalStackOf true (stack 21) = expand (instr 21) := by decide
theorem closed_21 : ∀ m : Fin 32, closedCheck 21 m := by decide

theorem instruction_22 : evalStackOf true (stack 22) = expand (instr 22) := by decide
theorem closed_22 : ∀ m : Fin 32, closedCheck 22 m := by decide

theorem instruction_23 : evalStackOf true (stack 23) = expand (instr 23) := by decide
theorem closed_23 : ∀ m : Fin 32, closedCheck 23 m := by decide

theorem instruction_24 : evalStackOf true (stack 24) = expand (instr 24) := by decide
theorem closed_24 : ∀ m : Fin 32, closedCheck 24 m := by decide

theorem instruction_25 : evalStackOf true (stack 25) = expand (instr 25) := by decide
theorem closed_25 : ∀ m : Fin 32, closedCheck 25 m := by decide

theorem instruction_26 : evalStackOf true (stack 26) = expand (instr 26) := by decide
theorem closed_26 : ∀ m : Fin 32, closedCheck 26 m := by decide

theorem instruction_27 : evalStackOf true (stack 27) = expand (instr 27) := by decide
theorem closed_27 : ∀ m : Fin 32, closedCheck 27 m := by decide

theorem instruction_28 : evalStackOf true (stack 28) = expand (instr 28) := by decide
theorem closed_28 : ∀ m : Fin 32, closedCheck 28 m := by decide

theorem instruction_29 : evalStackOf true (stack 29) = expand (instr 29) := by decide
theorem closed_29 : ∀ m : Fin 32, closedCheck 29 m := by decide

theorem instruction_30 : evalStackOf true (stack 30) = expand (instr 30) := by decide
theorem closed_30 : ∀ m : Fin 32, closedCheck 30 m := by decide

theorem instruction_31 : evalStackOf true (stack 31) = expand (instr 31) := by decide
theorem closed_31 : ∀ m : Fin 32, closedCheck 31 m := by decide

theorem instruction_32 : evalStackOf true (stack 32) = expand (instr 32) := by decide
theorem closed_32 : ∀ m : Fin 32, closedCheck 32 m := by decide

theorem instruction_33 : evalStackOf true (stack 33) = expand (instr 33) := by decide
theorem closed_33 : ∀ m : Fin 32, closedCheck 33 m := by decide

theorem instruction_34 : evalStackOf true (stack 34) = expand (instr 34) := by decide
theorem closed_34 : ∀ m : Fin 32, closedCheck 34 m := by decide

theorem instruction_35 : evalStackOf true (stack 35) = expand (instr 35) := by decide
theorem closed_35 : ∀ m : Fin 32, closedCheck 35 m := by decide

theorem instruction_36 : evalStackOf true (stack 36) = expand (instr 36) := by decide
theorem closed_36 : ∀ m : Fin 32, closedCheck 36 m := by decide

theorem instruction_37 : evalStackOf true (stack 37) = expand (instr 37) := by decide
theorem closed_37 : ∀ m : Fin 32, closedCheck 37 m := by decide

theorem instruction_38 : evalStackOf true (stack 38) = expand (instr 38) := by decide
theorem closed_38 : ∀ m : Fin 32, closedCheck 38 m := by decide

theorem instruction_39 : evalStackOf true (stack 39) = expand (instr 39) := by decide
theorem closed_39 : ∀ m : Fin 32, closedCheck 39 m := by decide

theorem instruction_40 : evalStackOf true (stack 40) = expand (instr 40) := by decide
theorem closed_40 : ∀ m : Fin 32, closedCheck 40 m := by decide

theorem instruction_41 : evalStackOf true (stack 41) = expand (instr 41) := by decide
theorem closed_41 : ∀ m : Fin 32, closedCheck 41 m := by decide

theorem instruction_42 : evalStackOf true (stack 42) = expand (instr 42) := by decide
theorem closed_42 : ∀ m : Fin 32, closedCheck 42 m := by decide

theorem instruction_43 : evalStackOf true (stack 43) = expand (instr 43) := by decide
theorem closed_43 : ∀ m : Fin 32, closedCheck 43 m := by decide

theorem instruction_44 : evalStackOf true (stack 44) = expand (instr 44) := by decide
theorem closed_44 : ∀ m : Fin 32, closedCheck 44 m := by decide

theorem instruction_45 : evalStackOf true (stack 45) = expand (instr 45) := by decide
theorem closed_45 : ∀ m : Fin 32, closedCheck 45 m := by decide

theorem instruction_46 : evalStackOf true (stack 46) = expand (instr 46) := by decide
theorem closed_46 : ∀ m : Fin 32, closedCheck 46 m := by decide

theorem instruction_47 : evalStackOf true (stack 47) = expand (instr 47) := by decide
theorem closed_47 : ∀ m : Fin 32, closedCheck 47 m := by decide

theorem instruction_48 : evalStackOf true (stack 48) = expand (instr 48) := by decide
theorem closed_48 : ∀ m : Fin 32, closedCheck 48 m := by decide

theorem instruction_49 : evalStackOf true (stack 49) = expand (instr 49) := by decide
theorem closed_49 : ∀ m : Fin 32, closedCheck 49 m := by decide

theorem instruction_50 : evalStackOf true (stack 50) = expand (instr 50) := by decide
theorem closed_50 : ∀ m : Fin 32, closedCheck 50 m := by decide

theorem instruction_51 : evalStackOf true (stack 51) = expand (instr 51) := by decide
theorem closed_51 : ∀ m : Fin 32, closedCheck 51 m := by decide

theorem instruction_52 : evalStackOf true (stack 52) = expand (instr 52) := by decide
theorem closed_52 : ∀ m : Fin 32, closedCheck 52 m := by decide

theorem instruction_53 : evalStackOf true (stack 53) = expand (instr 53) := by decide
theorem closed_53 : ∀ m : Fin 32, closedCheck 53 m := by decide

theorem instruction_54 : evalStackOf true (stack 54) = expand (instr 54) := by decide
theorem closed_54 : ∀ m : Fin 32, closedCheck 54 m := by decide

theorem instruction_55 : evalStackOf true (stack 55) = expand (instr 55) := by decide
theorem closed_55 : ∀ m : Fin 32, closedCheck 55 m := by decide

theorem instruction_56 : evalStackOf true (stack 56) = expand (instr 56) := by decide
theorem closed_56 : ∀ m : Fin 32, closedCheck 56 m := by decide

theorem instruction_57 : evalStackOf true (stack 57) = expand (instr 57) := by decide
theorem closed_57 : ∀ m : Fin 32, closedCheck 57 m := by decide

theorem instruction_58 : evalStackOf true (stack 58) = expand (instr 58) := by decide
theorem closed_58 : ∀ m : Fin 32, closedCheck 58 m := by decide

theorem instruction_59 : evalStackOf true (stack 59) = expand (instr 59) := by decide
theorem closed_59 : ∀ m : Fin 32, closedCheck 59 m := by decide

theorem instruction_60 : evalStackOf true (stack 60) = expand (instr 60) := by decide
theorem closed_60 : ∀ m : Fin 32, closedCheck 60 m := by decide

theorem instruction_61 : evalStackOf true (stack 61) = expand (instr 61) := by decide
theorem closed_61 : ∀ m : Fin 32, closedCheck 61 m := by decide

theorem instruction_62 : evalStackOf true (stack 62) = expand (instr 62) := by decide
theorem closed_62 : ∀ m : Fin 32, closedCheck 62 m := by decide

theorem instruction_63 : evalStackOf true (stack 63) = expand (instr 63) := by decide
theorem closed_63 : ∀ m : Fin 32, closedCheck 63 m := by decide

theorem instruction_64 : evalStackOf true (stack 64) = expand (instr 64) := by decide
theorem closed_64 : ∀ m : Fin 32, closedCheck 64 m := by decide

theorem instruction_65 : evalStackOf true (stack 65) = expand (instr 65) := by decide
theorem closed_65 : ∀ m : Fin 32, closedCheck 65 m := by decide

theorem instruction_66 : evalStackOf true (stack 66) = expand (instr 66) := by decide
theorem closed_66 : ∀ m : Fin 32, closedCheck 66 m := by decide

theorem instruction_67 : evalStackOf true (stack 67) = expand (instr 67) := by decide
theorem closed_67 : ∀ m : Fin 32, closedCheck 67 m := by decide

theorem instruction_68 : evalStackOf true (stack 68) = expand (instr 68) := by decide
theorem closed_68 : ∀ m : Fin 32, closedCheck 68 m := by decide

theorem instruction_69 : evalStackOf true (stack 69) = expand (instr 69) := by decide
theorem closed_69 : ∀ m : Fin 32, closedCheck 69 m := by decide

theorem instruction_70 : evalStackOf true (stack 70) = expand (instr 70) := by decide
theorem closed_70 : ∀ m : Fin 32, closedCheck 70 m := by decide

theorem instruction_71 : evalStackOf true (stack 71) = expand (instr 71) := by decide
theorem closed_71 : ∀ m : Fin 32, closedCheck 71 m := by decide

theorem instruction_72 : evalStackOf true (stack 72) = expand (instr 72) := by decide
theorem closed_72 : ∀ m : Fin 32, closedCheck 72 m := by decide

theorem instruction_73 : evalStackOf true (stack 73) = expand (instr 73) := by decide
theorem closed_73 : ∀ m : Fin 32, closedCheck 73 m := by decide

theorem instruction_74 : evalStackOf true (stack 74) = expand (instr 74) := by decide
theorem closed_74 : ∀ m : Fin 32, closedCheck 74 m := by decide

theorem instruction_75 : evalStackOf true (stack 75) = expand (instr 75) := by decide
theorem closed_75 : ∀ m : Fin 32, closedCheck 75 m := by decide

theorem instruction_76 : evalStackOf true (stack 76) = expand (instr 76) := by decide
theorem closed_76 : ∀ m : Fin 32, closedCheck 76 m := by decide

theorem instruction_77 : evalStackOf true (stack 77) = expand (instr 77) := by decide
theorem closed_77 : ∀ m : Fin 32, closedCheck 77 m := by decide

theorem instruction_78 : evalStackOf true (stack 78) = expand (instr 78) := by decide
theorem closed_78 : ∀ m : Fin 32, closedCheck 78 m := by decide

theorem instruction_79 : evalStackOf true (stack 79) = expand (instr 79) := by decide
theorem closed_79 : ∀ m : Fin 32, closedCheck 79 m := by decide

theorem instruction_80 : evalStackOf true (stack 80) = expand (instr 80) := by decide
theorem closed_80 : ∀ m : Fin 32, closedCheck 80 m := by decide

theorem instruction_81 : evalStackOf true (stack 81) = expand (instr 81) := by decide
theorem closed_81 : ∀ m : Fin 32, closedCheck 81 m := by decide

theorem instruction_82 : evalStackOf true (stack 82) = expand (instr 82) := by decide
theorem closed_82 : ∀ m : Fin 32, closedCheck 82 m := by decide

theorem instruction_83 : evalStackOf true (stack 83) = expand (instr 83) := by decide
theorem closed_83 : ∀ m : Fin 32, closedCheck 83 m := by decide

theorem instruction_84 : evalStackOf true (stack 84) = expand (instr 84) := by decide
theorem closed_84 : ∀ m : Fin 32, closedCheck 84 m := by decide

theorem instruction_85 : evalStackOf true (stack 85) = expand (instr 85) := by decide
theorem closed_85 : ∀ m : Fin 32, closedCheck 85 m := by decide

theorem instruction_86 : evalStackOf true (stack 86) = expand (instr 86) := by decide
theorem closed_86 : ∀ m : Fin 32, closedCheck 86 m := by decide

theorem instruction_87 : evalStackOf true (stack 87) = expand (instr 87) := by decide
theorem closed_87 : ∀ m : Fin 32, closedCheck 87 m := by decide

theorem instruction_88 : evalStackOf true (stack 88) = expand (instr 88) := by decide
theorem closed_88 : ∀ m : Fin 32, closedCheck 88 m := by decide

theorem instruction_89 : evalStackOf true (stack 89) = expand (instr 89) := by decide
theorem closed_89 : ∀ m : Fin 32, closedCheck 89 m := by decide

theorem instruction_90 : evalStackOf true (stack 90) = expand (instr 90) := by decide
theorem closed_90 : ∀ m : Fin 32, closedCheck 90 m := by decide

theorem instruction_91 : evalStackOf true (stack 91) = expand (instr 91) := by decide
theorem closed_91 : ∀ m : Fin 32, closedCheck 91 m := by decide

theorem instruction_92 : evalStackOf true (stack 92) = expand (instr 92) := by decide
theorem closed_92 : ∀ m : Fin 32, closedCheck 92 m := by decide

theorem instruction_93 : evalStackOf true (stack 93) = expand (instr 93) := by decide
theorem closed_93 : ∀ m : Fin 32, closedCheck 93 m := by decide

theorem instruction_94 : evalStackOf true (stack 94) = expand (instr 94) := by decide
theorem closed_94 : ∀ m : Fin 32, closedCheck 94 m := by decide

theorem instruction_95 : evalStackOf true (stack 95) = expand (instr 95) := by decide
theorem closed_95 : ∀ m : Fin 32, closedCheck 95 m := by decide

theorem instruction_96 : evalStackOf true (stack 96) = expand (instr 96) := by decide
theorem closed_96 : ∀ m : Fin 32, closedCheck 96 m := by decide

theorem instruction_97 : evalStackOf true (stack 97) = expand (instr 97) := by decide
theorem closed_97 : ∀ m : Fin 32, closedCheck 97 m := by decide

theorem instruction_98 : evalStackOf true (stack 98) = expand (instr 98) := by decide
theorem closed_98 : ∀ m : Fin 32, closedCheck 98 m := by decide

theorem instruction_99 : evalStackOf true (stack 99) = expand (instr 99) := by decide
theorem closed_99 : ∀ m : Fin 32, closedCheck 99 m := by decide

theorem instruction_100 : evalStackOf true (stack 100) = expand (instr 100) := by decide
theorem closed_100 : ∀ m : Fin 32, closedCheck 100 m := by decide

theorem instruction_101 : evalStackOf true (stack 101) = expand (instr 101) := by decide
theorem closed_101 : ∀ m : Fin 32, closedCheck 101 m := by decide

theorem instruction_102 : evalStackOf true (stack 102) = expand (instr 102) := by decide
theorem closed_102 : ∀ m : Fin 32, closedCheck 102 m := by decide

theorem instruction_103 : evalStackOf true (stack 103) = expand (instr 103) := by decide
theorem closed_103 : ∀ m : Fin 32, closedCheck 103 m := by decide

theorem instruction_104 : evalStackOf true (stack 104) = expand (instr 104) := by decide
theorem closed_104 : ∀ m : Fin 32, closedCheck 104 m := by decide

theorem instruction_105 : evalStackOf true (stack 105) = expand (instr 105) := by decide
theorem closed_105 : ∀ m : Fin 32, closedCheck 105 m := by decide

theorem instruction_106 : evalStackOf true (stack 106) = expand (instr 106) := by decide
theorem closed_106 : ∀ m : Fin 32, closedCheck 106 m := by decide

theorem instruction_107 : evalStackOf true (stack 107) = expand (instr 107) := by decide
theorem closed_107 : ∀ m : Fin 32, closedCheck 107 m := by decide

theorem instruction_108 : evalStackOf true (stack 108) = expand (instr 108) := by decide
theorem closed_108 : ∀ m : Fin 32, closedCheck 108 m := by decide

theorem instruction_109 : evalStackOf true (stack 109) = expand (instr 109) := by decide
theorem closed_109 : ∀ m : Fin 32, closedCheck 109 m := by decide

theorem instruction_110 : evalStackOf true (stack 110) = expand (instr 110) := by decide
theorem closed_110 : ∀ m : Fin 32, closedCheck 110 m := by decide

theorem instruction_111 : evalStackOf true (stack 111) = expand (instr 111) := by decide
theorem closed_111 : ∀ m : Fin 32, closedCheck 111 m := by decide

theorem instruction_112 : evalStackOf true (stack 112) = expand (instr 112) := by decide
theorem closed_112 : ∀ m : Fin 32, closedCheck 112 m := by decide

theorem instruction_113 : evalStackOf true (stack 113) = expand (instr 113) := by decide
theorem closed_113 : ∀ m : Fin 32, closedCheck 113 m := by decide

theorem instruction_114 : evalStackOf true (stack 114) = expand (instr 114) := by decide
theorem closed_114 : ∀ m : Fin 32, closedCheck 114 m := by decide

theorem instruction_115 : evalStackOf true (stack 115) = expand (instr 115) := by decide
theorem closed_115 : ∀ m : Fin 32, closedCheck 115 m := by decide

theorem instruction_116 : evalStackOf true (stack 116) = expand (instr 116) := by decide
theorem closed_116 : ∀ m : Fin 32, closedCheck 116 m := by decide

theorem instruction_117 : evalStackOf true (stack 117) = expand (instr 117) := by decide
theorem closed_117 : ∀ m : Fin 32, closedCheck 117 m := by decide

theorem instruction_118 : evalStackOf true (stack 118) = expand (instr 118) := by decide
theorem closed_118 : ∀ m : Fin 32, closedCheck 118 m := by decide

theorem instruction_119 : evalStackOf true (stack 119) = expand (instr 119) := by decide
theorem closed_119 : ∀ m : Fin 32, closedCheck 119 m := by decide

theorem instruction_120 : evalStackOf true (stack 120) = expand (instr 120) := by decide
theorem closed_120 : ∀ m : Fin 32, closedCheck 120 m := by decide

theorem instruction_exact (s : Fin 121) :
    evalStackOf true (stack s) = expand (instr s) := by
  fin_cases s
  · exact instruction_0
  · exact instruction_1
  · exact instruction_2
  · exact instruction_3
  · exact instruction_4
  · exact instruction_5
  · exact instruction_6
  · exact instruction_7
  · exact instruction_8
  · exact instruction_9
  · exact instruction_10
  · exact instruction_11
  · exact instruction_12
  · exact instruction_13
  · exact instruction_14
  · exact instruction_15
  · exact instruction_16
  · exact instruction_17
  · exact instruction_18
  · exact instruction_19
  · exact instruction_20
  · exact instruction_21
  · exact instruction_22
  · exact instruction_23
  · exact instruction_24
  · exact instruction_25
  · exact instruction_26
  · exact instruction_27
  · exact instruction_28
  · exact instruction_29
  · exact instruction_30
  · exact instruction_31
  · exact instruction_32
  · exact instruction_33
  · exact instruction_34
  · exact instruction_35
  · exact instruction_36
  · exact instruction_37
  · exact instruction_38
  · exact instruction_39
  · exact instruction_40
  · exact instruction_41
  · exact instruction_42
  · exact instruction_43
  · exact instruction_44
  · exact instruction_45
  · exact instruction_46
  · exact instruction_47
  · exact instruction_48
  · exact instruction_49
  · exact instruction_50
  · exact instruction_51
  · exact instruction_52
  · exact instruction_53
  · exact instruction_54
  · exact instruction_55
  · exact instruction_56
  · exact instruction_57
  · exact instruction_58
  · exact instruction_59
  · exact instruction_60
  · exact instruction_61
  · exact instruction_62
  · exact instruction_63
  · exact instruction_64
  · exact instruction_65
  · exact instruction_66
  · exact instruction_67
  · exact instruction_68
  · exact instruction_69
  · exact instruction_70
  · exact instruction_71
  · exact instruction_72
  · exact instruction_73
  · exact instruction_74
  · exact instruction_75
  · exact instruction_76
  · exact instruction_77
  · exact instruction_78
  · exact instruction_79
  · exact instruction_80
  · exact instruction_81
  · exact instruction_82
  · exact instruction_83
  · exact instruction_84
  · exact instruction_85
  · exact instruction_86
  · exact instruction_87
  · exact instruction_88
  · exact instruction_89
  · exact instruction_90
  · exact instruction_91
  · exact instruction_92
  · exact instruction_93
  · exact instruction_94
  · exact instruction_95
  · exact instruction_96
  · exact instruction_97
  · exact instruction_98
  · exact instruction_99
  · exact instruction_100
  · exact instruction_101
  · exact instruction_102
  · exact instruction_103
  · exact instruction_104
  · exact instruction_105
  · exact instruction_106
  · exact instruction_107
  · exact instruction_108
  · exact instruction_109
  · exact instruction_110
  · exact instruction_111
  · exact instruction_112
  · exact instruction_113
  · exact instruction_114
  · exact instruction_115
  · exact instruction_116
  · exact instruction_117
  · exact instruction_118
  · exact instruction_119
  · exact instruction_120

theorem finite_closed (s : Fin 121) (m : Fin 32) : closedCheck s m := by
  fin_cases s
  · exact closed_0 m
  · exact closed_1 m
  · exact closed_2 m
  · exact closed_3 m
  · exact closed_4 m
  · exact closed_5 m
  · exact closed_6 m
  · exact closed_7 m
  · exact closed_8 m
  · exact closed_9 m
  · exact closed_10 m
  · exact closed_11 m
  · exact closed_12 m
  · exact closed_13 m
  · exact closed_14 m
  · exact closed_15 m
  · exact closed_16 m
  · exact closed_17 m
  · exact closed_18 m
  · exact closed_19 m
  · exact closed_20 m
  · exact closed_21 m
  · exact closed_22 m
  · exact closed_23 m
  · exact closed_24 m
  · exact closed_25 m
  · exact closed_26 m
  · exact closed_27 m
  · exact closed_28 m
  · exact closed_29 m
  · exact closed_30 m
  · exact closed_31 m
  · exact closed_32 m
  · exact closed_33 m
  · exact closed_34 m
  · exact closed_35 m
  · exact closed_36 m
  · exact closed_37 m
  · exact closed_38 m
  · exact closed_39 m
  · exact closed_40 m
  · exact closed_41 m
  · exact closed_42 m
  · exact closed_43 m
  · exact closed_44 m
  · exact closed_45 m
  · exact closed_46 m
  · exact closed_47 m
  · exact closed_48 m
  · exact closed_49 m
  · exact closed_50 m
  · exact closed_51 m
  · exact closed_52 m
  · exact closed_53 m
  · exact closed_54 m
  · exact closed_55 m
  · exact closed_56 m
  · exact closed_57 m
  · exact closed_58 m
  · exact closed_59 m
  · exact closed_60 m
  · exact closed_61 m
  · exact closed_62 m
  · exact closed_63 m
  · exact closed_64 m
  · exact closed_65 m
  · exact closed_66 m
  · exact closed_67 m
  · exact closed_68 m
  · exact closed_69 m
  · exact closed_70 m
  · exact closed_71 m
  · exact closed_72 m
  · exact closed_73 m
  · exact closed_74 m
  · exact closed_75 m
  · exact closed_76 m
  · exact closed_77 m
  · exact closed_78 m
  · exact closed_79 m
  · exact closed_80 m
  · exact closed_81 m
  · exact closed_82 m
  · exact closed_83 m
  · exact closed_84 m
  · exact closed_85 m
  · exact closed_86 m
  · exact closed_87 m
  · exact closed_88 m
  · exact closed_89 m
  · exact closed_90 m
  · exact closed_91 m
  · exact closed_92 m
  · exact closed_93 m
  · exact closed_94 m
  · exact closed_95 m
  · exact closed_96 m
  · exact closed_97 m
  · exact closed_98 m
  · exact closed_99 m
  · exact closed_100 m
  · exact closed_101 m
  · exact closed_102 m
  · exact closed_103 m
  · exact closed_104 m
  · exact closed_105 m
  · exact closed_106 m
  · exact closed_107 m
  · exact closed_108 m
  · exact closed_109 m
  · exact closed_110 m
  · exact closed_111 m
  · exact closed_112 m
  · exact closed_113 m
  · exact closed_114 m
  · exact closed_115 m
  · exact closed_116 m
  · exact closed_117 m
  · exact closed_118 m
  · exact closed_119 m
  · exact closed_120 m

end ConjectureMachines.Riemann104.PhaseB1
