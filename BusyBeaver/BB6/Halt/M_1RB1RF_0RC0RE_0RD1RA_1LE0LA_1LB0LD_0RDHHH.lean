/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

@[simp] theorem isFlipped_tm : BusyBeaver.RleStackEngine.isFlipped target_tm = true := rfl

namespace Solution

open BusyBeaver.RleStackEngine

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, r, l⟩⟩

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, listblank_append_cons,
    listblank_append_nil, zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one,
    encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]
  try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, listblank_append_cons,
    listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

theorem init_reaches_stack : (init []) [target_tm]⊢⁺ (cfg_C target_tm [] [0]) := by
  rw [init_nil]; unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero, encLeft_nil, encRight_nil]; execute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) []) := by
  unfold cfg_B cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_nil]; execute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_B target_tm (0 :: L) R) := by
  unfold cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero R, encRight_zero L];
      execute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR target_tm L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ d R, encLeft_zero (d :: R), encLeft_expose d R]; execute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_BR target_tm (0 :: L) R) := by
  unfold cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero R, encRight_zero L];
      execute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢⁺ (cfg_DR0 target_tm L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ 0 R,
      encLeft_zero R]; execute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_B target_tm (bumpHead L) (d :: R)) :=
        by
  unfold cfg_BR cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ (d + 1) R, encLeft_succ d R, encLeft_expose d R]; execute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢⁺ (cfg_C target_tm [1] R) := by
  unfold cfg_DR0 cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_nil, encRight_succ 0 [], encRight_zero [], encRight_nil]; execute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (0 :: R)) := by
  unfold cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero L, encLeft_zero R];
      execute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ a L,
      encLeft_zero R]; execute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢⁺ (cfg_DR0 target_tm [] R) := by
  unfold cfg_C cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_nil]; execute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢⁺ (cfg_C target_tm [] (1 :: R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]; execute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) (1 :: R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero (0 :: L), encRight_zero L, encLeft_succ 0 R, encLeft_zero R]; execute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢⁺
    (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero (1 :: L), encRight_succ 0 L, encRight_zero L, encLeft_zero (bumpHead R)]
  execute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢⁺ (cfg_BR target_tm (a :: L) (0 :: 1 ::
        R)) := by
  unfold cfg_C cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero ((a + 2) :: L), encRight_succ (a + 1) L, encRight_succ a L,
    encLeft_zero (1 :: R), encLeft_succ 0 R, encLeft_zero R]; execute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢⁺ (cfg_B target_tm [0] (1 :: R)) := by
  unfold cfg_C cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ 0 [], encRight_zero [], encRight_nil, encLeft_succ 0 R, encLeft_zero R]
  execute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (2 :: R)) := by
  unfold cfg_C cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ 0 (0 :: L), encRight_zero (0 :: L), encRight_zero L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; execute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (2 :: R)) :=
        by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ 0 ((a + 1) :: L), encRight_zero ((a + 1) :: L), encRight_succ a L,
    encLeft_succ 1 R, encLeft_succ 0 R, encLeft_zero R]; execute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢⁺
    (cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R)) := by
  unfold cfg_C cfg_Halt; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ (a + 1) L, encRight_succ a L, encRight_expose a L]; execute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt (((encRight1 L).cons 0) <+ (([1] : List (Fin 2)) ^ a))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft1 R),
   rule_C_add_two_step a L R, rfl⟩


instance : HasRleStackRules target_tm where
  rule_B_nil := rule_B_nil
  rule_B_zero := rule_B_zero
  rule_B_succ := rule_B_succ
  rule_BR_nil := rule_BR_nil
  rule_BR_zero := rule_BR_zero
  rule_BR_one := rule_BR_one
  rule_BR_add_two := rule_BR_add_two
  rule_DR0_nil := rule_DR0_nil
  rule_DR0_zero := rule_DR0_zero
  rule_DR0_succ := rule_DR0_succ
  rule_C_nil := rule_C_nil
  rule_C_zero_nil := rule_C_zero_nil
  rule_C_zero_zero := rule_C_zero_zero
  rule_C_zero_one := rule_C_zero_one
  rule_C_zero_add_two := rule_C_zero_add_two
  rule_C_one_nil := rule_C_one_nil
  rule_C_one_zero := rule_C_one_zero
  rule_C_one_succ := rule_C_one_succ
  rule_C_add_two_halt := rule_C_add_two_halt

def ckpt0 : RleFullState := ⟨.C, .raw [], [.z 1], false⟩

def ckpt6 : RleFullState := ⟨.C, .raw [.z 1, .k 281358 77415, .k 142094 1, .k 2229006 1, .k
    4440846 48275, .k 29606670 1, .k 17023758 33721, .k 50578190 1, .k 79938318 980, .k 265280270
    1, .k 319753998 203, .k 386862862 1, .k 521080590 6175, .k 789516046 1, .k 1326386958 309, .k
    2270693102 1, .k 5305547838 277, .k 1110974254 1, .k 67113177358 1, .k 84888764430 263, .k
    230838460430 1, .k 339555069966 5, .k 860299088330 1, .k 1358220279870 92, .k 2457731907646 1
    , .k 4656755163198 20, .k 4540718317493 1, .k 1856589531279 1, .z 2], [.k 150286 1, .k 84750
    876511, .k 51982 1, .k 35598 1737322, .k 19214 1, .k 11022 38203784, .k 8974 1, .k 7950
    27434495, .k 4878 42087863, .k 2830 1, .k 1806 73686092, .k 526 1, .k 142 1, .k 174 475716378
    , .k 110 1, .k 78 13551424202, .k 126 1, .k 30 505632912192, .k 14 1, .k 6 47526570402450, .k
    4 1, .k 3 57901138422179, .z 3, .d 2, .k 0 37610989893458, .d 2], false⟩

def ckpt12 : RleFullState := ⟨.BR, .clean 3 [(5399298, 13551424202), (7496450, 1), (11690754,
    475716378), (9593602, 1), (34759426, 1), (118645506, 73686092), (185754370, 1), (319972098,
    42087863), (521298690, 27434495), (588407554, 1), (722625282, 38203784), (1259496194, 1),
    (2333238018, 1737322), (3406979842, 1), (5554463490, 876511), (9849430786, 1), (18439365378,
    77415), (9312559874, 1), (146080424706, 1), (291035570946, 48275), (1940303012610, 1),
    (1115669291778, 32810), (1394586614730, 1), (278917322970, 909), (828673136858, 1),
    (1309709474010, 980), (4346352015578, 1), (5238849575130, 203), (6338361202906, 1),
    (8537384458458, 6175), (12935430969562, 1), (21731523991770, 309), (37203035855066, 1),
    (86926095849690, 277), (18202202249434, 1), (1099582297905370, 1), (1390817516493018, 263),
    (3782057335757018, 1), (5563270266394842, 5), (14095140263270618, 1), (22253081065461978, 6),
    (81803770100545754, 1), (89012324261841114, 8), (190258379573867327, 1), (356049297047364462,
    69), (73427410834671118, 1), (4521950179403093518, 1), (5425513671652212490, 1),
    (4340401297689886786, 1), (91148620044125286401, 1), (15, 1), (1458377920706004582399, 2)]
    364594480176501145522, [.k 8545026 1, .k 2253570 505632912192, .k 1204994 1, .k 680706
    26720150428303, .k 336210 1, .k 21536 1, .k 42549 20806419974146, .k 34357 1, .k 30261
    57901138422180, .k 17973 37610989893458, .k 9781 1, .k 5685 30716371615732, .k 3637 1, .k 2613
    305490132233582, .k 5685 1, .k 4149 270647459772345, .k 3925 1, .k 22 1, .k 267
    139989328324157, .k 107 1, .k 24 1, .k 30 781492533683413, .k 26 1, .k 15 271475135198707, .k
    13 1, .k 12 48671766179730583, .k 15 1, .k 9 94767307651599602, .k 12 1, .k 6
    331887753716974115, .k 3 744220640956988995, .k 1 1, .k 0 18310355970030908204, .d 2], false⟩

def ckpt18 : RleFullState := ⟨.DR0, .raw [.z 3], [.d 1, .z 637191343783878439541550, .d 2, .d 1,
    .k 53511727938691907386159 1, .k 93336186925184309857071 9, .k 55083803111267391840815 1, .k
    23334046731296077464111 50, .k 12468773163752969224751 1, .k 5833511682824019329583 8, .k
    5361091877309366616623 1, .k 1458377920706116272687 6, .k 923739112293703303727 1, .k
    364594480178452447791 5, .k 247860909556172014127 1, .k 91148616760886510127 263, .k
    72062225475526410799 1, .k 1192899526618989103 1, .k 5696788617605366319 277, .k
    2438138157797687855 1, .k 1424197156324721199 309, .k 847736404021297711 1, .k
    559506027869585967 6175, .k 415390839793730095 1, .k 343333245755802159 203, .k
    284842525693002287 1, .k 85833120088801839 980, .k 54307922697208367 1, .k 18279125678244399
    909, .k 91395628383027759 1, .k 73116502706045487 8, .k 18279125676510767 1, .k
    18279125676511791 32801, .k 31789924558623279 1, .k 4768326794400303 48275, .k
    2393381678404143 1, .k 152576980996655 1, .k 302110562374191 77415, .k 161373074018863 1, .k
    91004329841199 876511, .k 55819957752367 1, .k 38227771707951 1737322, .k 20635585663535 1, .k
    11839492641327 38203784, .k 9640469385775 1, .k 8540957757999 27434495, .k 5242422874671
    42087863, .k 3043399619119 1, .k 1943887991343 73686092, .k 569498456623 1, .k 157181596207 1
    , .k 191541334575 475716378, .k 122821857839 1, .k 88462119471 13551424202, .k 140001727023 1
    , .k 36922511919 505632912192, .k 19742642735 1, .k 11152708143 24723210206458, .z 9034176083
    , .d 1, .z 529633014, .d 2, .d 1, .k 2788177035 1996940221844, .k 1377121419 1, .k 88216715 1
    , .k 174285963 20806419974146, .k 140731531 1, .k 123954315 57901138422180, .k 73622667
    37610989893458, .k 40068235 1, .k 23291019 30716371615732, .k 14902411 1, .k 10708107
    305490132233582, .k 23291019 1, .k 16999563 270647459772345, .k 16082059 1, .k 95371 1, .k
    1098891 139989328324157, .k 443531 1, .k 103563 1, .k 128139 781492533683413, .k 111755 1, .k
    66699 271475135198707, .k 58507 1, .k 54411 48671766179730583, .k 66699 1, .k 42123
    94767307651599602, .k 54411 1, .k 29835 331887753716974115, .k 17547 744220640956988995, .k
    9355 1, .k 5259 382904836146532053728, .k 3211 1, .k 2187 210157523808992004318, .k 1931 1, .k
    651 2160111270177901513702, .k 523 1, .k 459 660481848050345900758, .z 87, .d 1, .z 92, .d 2,
    .d 1, .k 114 9040449275367983386986, .k 66 906038693021585505429, .k 41 1, .k 15
    6063759545596197098728, .k 7 1, .k 3 30646279106479104971761, .k 1 1, .k 0
    1009331069384952120084451, .d 2], false⟩

def ckpt24 : RleFullState := ⟨.C, .raw [.z 1, .k 11175430935936220053061216 1, .k
    203498126670575412323054098 1, .k 382305021645554933172033474 33, .k
    188683387653217877438607425 1, .z 2], [.k 23894063852847183323252097 4, .k
    10778816692974141806191745 1, .k 5973515963211795830813313 8, .k 3192005929920760121537153 1,
    .k 1493378990802948948374145 8, .k 1372439520591197853856385 1, .k 373344747700765765808769 6
    , .k 236477212747188045755009 1, .k 93336186925683826635393 5, .k 63452392846380035617409 1,
    .k 23334045890786946593409 263, .k 18447929721734761165441 1, .k 305382278814461211265 1, .k
    1458377886106973778561 277, .k 624163368396208091777 1, .k 364594472019128627841 309, .k
    217020519429452214913 1, .k 143233543134614008449 6175, .k 106340054987194905217 1, .k
    87893310913485353601 203, .k 72919686577408586369 1, .k 21973278742733271681 980, .k
    13902828210485342849 1, .k 4679456173630567041 909, .k 23397280866055107201 1, .k
    18717824692747645569 8, .k 4679456173186757249 1, .k 4679456173187019393 32801, .k
    8138220687007560321 1, .k 1220691659366478465 48275, .k 612705709671461505 1, .k
    39059707135144577 1, .k 77340303967793793 77415, .k 41311506948829825 1, .k 23297108439347841
    876511, .k 14289909184606849 1, .k 9786309557236353 1737322, .k 5282709929865857 1, .k
    3030910116180609 38203784, .k 2467960162759297 1, .k 2186485186048641 27434495, .k
    1342060255916673 42087863, .k 779110302495361 1, .k 497635325784705 73686092, .k
    145791604896385 1, .k 40238488629889 1, .k 49034581652097 475716378, .k 31442395607681 1, .k
    22646302585473 13551424202, .k 35840442118785 1, .k 9452163052161 505632912192, .k
    5054116541057 1, .k 2855093285505 26720150428303, .k 1410172334721 1, .k 90333917825 1, .k
    178468827777 20806419974146, .k 144109089409 1, .k 126929220225 57901138422180, .k 75389612673
    37610989893458, .k 41029874305 1, .k 23850005121 30716371615732, .k 15260070529 1, .k
    10965103233 305490132233582, .k 23850005121 1, .k 17407554177 270647459772345, .k 16468030081
    1, .k 97661569 1, .k 1125266049 139989328324157, .k 454177409 1, .k 106050177 1, .k 131216001
    781492533683413, .k 114438785 1, .k 68301441 271475135198707, .k 59912833 1, .k 55718529
    48671766179730583, .k 68301441 1, .k 43135617 94767307651599602, .k 55718529 1, .k 30552705
    331887753716974115, .k 17969793 744220640956988995, .k 9581185 1, .k 5386881
    7072824145170092509, .k 5265677 1, .k 1346721 176244060668935040975, .k 350513 1, .k 336681
    67361141208737850269, .k 123857 1, .k 84189 132226810123689069972, .k 51421 1, .k 35037
    210157523808992004318, .k 30941 1, .k 10461 2160111270177901513702, .k 8413 1, .k 7389
    660481848050345900758, .k 1437 1, .k 413 1, .k 501 9040449275367983386986, .k 309
    906038693021585505429, .k 209 1, .k 105 6063759545596197098728, .k 73 1, .k 57
    30646279106479104971761, .k 49 1, .k 45 1009331069384952120084451, .k 57 1, .k 33
    7537176816673596729879974, .k 21 5622837964162795894755808, .k 13 1, .k 9
    39547083232249886800713772, .k 5 1, .k 3 654276377082664764984814935, .k 6 1, .k 0
    1615416730339319185619342344, .d 2], false⟩

def ckpt30 : RleFullState := ⟨.C, .raw [.z 1, .k 817153518059714591113512431 1, .k
    1529220086582219732688209391 8, .k 2759377073401380302385087983 1, .k
    6116880346328878930752538095 4, .k 2860910319599672333583672559 1, .k
    52095520427667305554701850351 1, .k 97870085541262062892040570607 8, .k
    259531341126341969520301487855 1, .k 391480342165048251568162282479 3, .k
    1513521437247345871367607986543 1, .k 1565921368660193006272649129967 4, .k
    4190496403530834217529157521375 1, .k 6263685474640772025090596519919 2, .k
    2515196707816662475441974916831 1, .z 2], [.k 382305021645554930783782383 8, .k
    351344517271346650587235823 1, .k 95576255411396036047046127 6, .k 60538166463280139713283567
    1, .k 23894063852975059618661871 5, .k 16243812568673289118057967 1, .k
    5973515748041458327913967 263, .k 4722670008764098858354159 1, .k 78177863376502070085103 1,
    .k 373344738843385287312879 277, .k 159785822309429271496175 1, .k 93336184836896928728559 309
    , .k 55557252973939767018991 1, .k 36667787042461186164207 6175, .k 27223054076721895736815 1
    , .k 22500687593852250523119 203, .k 18667439763816598111727 1, .k 5625159358139717551599 980
    , .k 3559124021884247770607 1, .k 1197940780449425163759 909, .k 5989703901710107444719 1, .k
    4791763121343397266927 8, .k 1197940780335809857007 1, .k 1197940780335876965871 32801, .k
    2083384495873935443439 1, .k 312497064797818488303 48275, .k 156852661675894146543 1, .k
    9999285026597012975 1, .k 19799117815755212271 77415, .k 10575745778900436463 1, .k
    5964059760473048559 876511, .k 3658216751259354607 1, .k 2505295246652507631 1737322, .k
    1352373742045660655 1, .k 775912989742237167 38203784, .k 631797801666381295 1, .k
    559740207628453359 27434495, .k 343567425514669551 42087863, .k 199452237438813679 1, .k
    127394643400885743 73686092, .k 37322650853475823 1, .k 10301053089252847 1, .k
    12552852902938095 475716378, .k 8049253275567599 1, .k 5797453461882351 13551424202, .k
    9175153182410223 1, .k 2419753741354479 505632912192, .k 1293853834511855 1, .k
    730903881090543 26720150428303, .k 361004117689839 1, .k 23125482964463 1, .k 45688019912175
    20806419974146, .k 36891926889967 1, .k 32493880378863 57901138422180, .k 19299740845551
    37610989893458, .k 10503647823343 1, .k 6105601312239 30716371615732, .k 3906578056687 1, .k
    2807066428911 305490132233582, .k 6105601312239 1, .k 4456333870575 270647459772345, .k
    4215815701999 1, .k 25001362927 1, .k 288068109807 139989328324157, .k 116269417967 1, .k
    27148846575 1, .k 33591297519 781492533683413, .k 29296330223 1, .k 17485170159
    271475135198707, .k 15337686511 1, .k 14263944687 48671766179730583, .k 17485170159 1, .k
    11042719215 94767307651599602, .k 14263944687 1, .k 7821493743 331887753716974115, .k
    4600268271 744220640956988995, .k 2452784623 1, .k 1379042799 7072824145170092509, .k
    1348014575 1, .k 344761839 176244060668935040975, .k 89732591 1, .k 86191599
    67361141208737850269, .k 31708655 1, .k 21553647 132226810123689069972, .k 13165039 1, .k
    8970735 210157523808992004318, .k 7922159 1, .k 2679279 2160111270177901513702, .k 2154991 1,
    .k 1892847 660481848050345900758, .k 369135 1, .k 106991 1, .k 129519 9040449275367983386986,
    .k 80367 906038693021585505429, .k 54767 1, .k 28143 6063759545596197098728, .k 19951 1, .k
    15855 30646279106479104971761, .k 13807 1, .k 12783 1009331069384952120084451, .k 15855 1, .k
    9711 7537176816673596729879974, .k 6639 5622837964162795894755808, .k 4591 1, .k 3567
    39547083232249886800713772, .k 2543 1, .k 2031 538559066387679221350882238, .k 1583 1, .k 495
    115717310694985543633932696, .k 687 1, .k 303 1615416730339319185619342344, .k 495 1, .k 111
    274784465758569372306465281757, .k 79 1, .k 63 507674404248318560861238978904, .k 111 1, .k 15
    2504802967801580957720172775389, .k 7 1, .k 3 6623541416857744891568440848885, .k 1 1, .k 0
    4682218824069723167996109957596, .d 2], false⟩

-- Each chunk reduces 120 (or 140) RLE batches in the kernel via `rfl`.
set_option maxRecDepth 2000000 in
theorem chunk_0 : runBatches 120 ckpt0 = ckpt6 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_1 : runBatches 120 ckpt6 = ckpt12 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_2 : runBatches 120 ckpt12 = ckpt18 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_3 : runBatches 120 ckpt18 = ckpt24 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_4 : runBatches 120 ckpt24 = ckpt30 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_5 : (runBatches 140 ckpt30).halted = true := rfl

theorem reach_30 : StateHalts target_tm ckpt30 :=
  runBatches_halts 140 ckpt30 (Or.inl chunk_5)
theorem reach_24 : StateHalts target_tm ckpt24 := chunk_back_batches chunk_4 reach_30
theorem reach_18 : StateHalts target_tm ckpt18 := chunk_back_batches chunk_3 reach_24
theorem reach_12 : StateHalts target_tm ckpt12 := chunk_back_batches chunk_2 reach_18
theorem reach_6 : StateHalts target_tm ckpt6 := chunk_back_batches chunk_1 reach_12
theorem reach_0 : StateHalts target_tm ckpt0 := chunk_back_batches chunk_0 reach_6

end Solution

public section

open Solution BusyBeaver.RleStackEngine in
theorem is_halt : IsHalt target := by
  rcases reach_0 with hfalse | hcan
  · simp [ckpt0] at hfalse
  · exact canHalt_of_stepPlus init_reaches_stack hcan

end

end BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH
