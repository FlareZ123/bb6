import SourceExactMItemPrefix424

/-!
# F424 symbolic checkpoint trace

The checkpoint states and kernel computation proofs below are extracted from
the pinned upstream Cryptids F424 certificate, but are kept separate from its
large collection of primitive halting certificates. This module only records
the symbolic stepSym trajectory from initSymCyc3 through symChk70511.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

def symChk4096_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12
      69932, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item
      (.run 1), .repB1 349284, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1)])

def symChk8192_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .rep12 293731192, .item (.run 2), .repB1 1468655224, .item (.run 0)],
      [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 6), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item .zero
      , .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk12288_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 7401584263016, .item (.run 1), .item (.run 1), .item (.run 0)
      , .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item .zero, .item (.run
      7401584264101), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      2), .item (.run 3), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero, .item (.run
      0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1)])

def symChk16384_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 0), .item (.run 1), .rep2 5828399623694162, .item (.run 1), .item (.run 0),
      .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 2), .repB1 11656799247386921, .item (.run 0)], [.item (.run 0)
      , .item (.run 11656799247388309), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 2), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 3), .item (.run 3), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 5), .item (.run 3), .item (.run 1), .item (.run 1)])

def symChk20480_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .rep12 9179181364734787724, .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 45895906823673936877, .item
      (.run 0)], [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1)])

def symChk24576_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.repB1 192751300452273201788429, .item (.run 0)], [.item (.run 0), .item (.run 0), .item
      (.run 1), .item (.run 1), .rep12 38550260090454640358104, .item (.run 0), .item (.run 2),
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 0), .item (.run 1)
      , .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero
      , .item (.run 3), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1)])

def symChk28672_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .rep12 161901426063024309850221340, .item (.run 2)
      , .repB1 809507130315121549251104250, .item (.run 0)], [.item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      5), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1)])

def symChk32768_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .repB1
      3399726966787864888523559563277, .item (.run 0)], [.item (.run 0), .item (.run 1), .item
      (.run 1), .rep12 679945393357572977704711913207, .item (.run 0), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 4), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1),
      .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk36864_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 2), .repB1 8566800475893506045311193103085396, .item (.run 0)], [.item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2
      4283400237946753022655596551544268, .item (.run 0), .item (.run 1), .item .zero, .item (.run
      8566800475893506045311193103088524), .item (.run 1), .item (.run 2), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1),
      .item (.run 1)])

def symChk40960_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .repB1 59964023182123780301115281865963814445, .item (.run 0)], [.item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .rep12 11992804636424756060223056373192763585, .item (.run 0), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 2), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 2), .item (.run 3), .item (.run 1), .item (.run 7), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1)])

def symChk45056_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .rep12
      28331309434081290173749125880312046958998, .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 0), .item .zero, .item (.run 1), .repB1
      141656547170406450868745629401560234791159, .item (.run 0)], [.item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero
      , .item (.run 7), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk49152_F424 : SymMode × List SymTok × List SymTok :=
  (.BB, [.item (.run 0), .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 1), .repB1 535429780494748407225024473657428158523986309, .item (.run 0)],
      [.item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      535429780494748407225024473657428158523990526), .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1)])

def symChk53248_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 1873892351078590533629325742230370269117066257558, .item (.run
      0), .item (.run 2), .item (.run 0), .item (.run 1), .item (.run 1), .rep12
      374778470215718106725865148446074053823413252433, .item (.run 0), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 6), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 5), .item (.run 1), .item (.run 6), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk57344_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .rep2
      996031434861122243531684763682732439419162283857463, .item (.run 1), .item (.run 0), .item
      .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      .zero, .item (.run 1), .repB1 1992062869722244487063369527365464878838324567709997, .item
      (.run 0)], [.item (.run 1992062869722244487063369527365464878838324567714920), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk61440_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .rep12 661776688146251534887371767366373046443244305364132822,
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)
      , .repB1 3308883440731257674436858836831865232216221526820658827, .item (.run 0)], [.item
      (.run 4), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
      .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 2), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk65536_F424 : SymMode × List SymTok × List SymTok :=
  (.DL, [.rep12 659540004931999983852102031802319817808504446014405329671, .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1
      3297700024659999919260510159011599089042522230072026642750, .item (.run 0)], [.item (.run 0)
      , .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 2), .item (.run 4), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item .zero, .item (.run 1), .item (.run 3), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk69632_F424 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1
      2629243525178812812679392664523750958759518709707280000200843, .item (.run 0)], [.item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2
      1314621762589406406339696332261875479379759354853640000103353, .item (.run 0), .item (.run
      1), .item (.run 2), .item (.run
      2629243525178812812679392664523750958759518709707280000206708), .item (.run 1), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk70511_F424 : SymMode × List SymTok × List SymTok :=
  (.HALT, [.item .zero, .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12
      2077426982857333580388655932463210634081595029892171852015193, .item (.run 2), .repB1
      10387134914286667901943279662316053170407975149460859260070043, .item (.run 0)], [.item
      (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
      .item (.run 1), .item .zero, .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1)
      , .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1)])

set_option maxRecDepth 200000 in
theorem sym_chk1_F424 : stepSym4096 initSymCyc3_F424 = symChk4096_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk2_F424 : stepSym4096 symChk4096_F424 = symChk8192_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk3_F424 : stepSym4096 symChk8192_F424 = symChk12288_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk4_F424 : stepSym4096 symChk12288_F424 = symChk16384_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk5_F424 : stepSym4096 symChk16384_F424 = symChk20480_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk6_F424 : stepSym4096 symChk20480_F424 = symChk24576_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk7_F424 : stepSym4096 symChk24576_F424 = symChk28672_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk8_F424 : stepSym4096 symChk28672_F424 = symChk32768_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk9_F424 : stepSym4096 symChk32768_F424 = symChk36864_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk10_F424 : stepSym4096 symChk36864_F424 = symChk40960_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk11_F424 : stepSym4096 symChk40960_F424 = symChk45056_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk12_F424 : stepSym4096 symChk45056_F424 = symChk49152_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk13_F424 : stepSym4096 symChk49152_F424 = symChk53248_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk14_F424 : stepSym4096 symChk53248_F424 = symChk57344_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk15_F424 : stepSym4096 symChk57344_F424 = symChk61440_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk16_F424 : stepSym4096 symChk61440_F424 = symChk65536_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk17_F424 : stepSym4096 symChk65536_F424 = symChk69632_F424 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk18_F424 : iterStep stepSym 15 (iterStep stepSym16 6 (iterStep stepSym256 3 symChk69632_F424))
    = symChk70511_F424 := by decide +kernel

/-- The 17 complete 4096-step checkpoints plus the final 879-step suffix
    give the exact 70,511-step symbolic trajectory. -/
theorem symRunF424_exact :
    iterStep stepSym 70511 initSymCyc3_F424 = symChk70511_F424 := by
  have h17 : iterStep stepSym (4096 * 17) initSymCyc3_F424 =
      symChk69632_F424 := by
    have hblocks : iterStep stepSym4096 17 initSymCyc3_F424 =
        symChk69632_F424 := by
      simp [iterStep, sym_chk1_F424, sym_chk2_F424, sym_chk3_F424,
        sym_chk4_F424, sym_chk5_F424, sym_chk6_F424, sym_chk7_F424,
        sym_chk8_F424, sym_chk9_F424, sym_chk10_F424, sym_chk11_F424,
        sym_chk12_F424, sym_chk13_F424, sym_chk14_F424, sym_chk15_F424,
        sym_chk16_F424, sym_chk17_F424]
    simpa [stepSym4096, stepSym256, stepSym16, iterStep_repeat] using hblocks
  have h18 : iterStep stepSym 879 symChk69632_F424 =
      symChk70511_F424 := by
    simpa [stepSym16, stepSym256, iterStep_repeat, iterStep_comp,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sym_chk18_F424
  calc
    iterStep stepSym 70511 initSymCyc3_F424 =
        iterStep stepSym (879 + 4096 * 17) initSymCyc3_F424 := by norm_num
    _ = iterStep stepSym 879
        (iterStep stepSym (4096 * 17) initSymCyc3_F424) :=
          (iterStep_comp stepSym 879 (4096 * 17) initSymCyc3_F424).symm
    _ = iterStep stepSym 879 symChk69632_F424 := by rw [h17]
    _ = symChk70511_F424 := h18

#print axioms symRunF424_exact

/-- The final symbolic state is in HALT mode and exposes the DL/zero halt
    transition as one original-machine step. -/
theorem step_DL_zero_halt_F424 (L1 R1 : List MItem) :
    (cfgDL target_tm (.zero :: L1) (.run 0 :: R1)) [target_tm]⊢⁺
      ⟨some E, ⟨1, (1 : Fin 2) >> encM L1, (0 : Fin 2) >> encM R1⟩⟩ := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  execute 1

theorem step_DL_zero_halt_F424_exact (L1 R1 : List MItem) :
    ReachesIn target_tm 1
      (cfgDL target_tm (.zero :: L1) (.run 0 :: R1))
      ⟨some E, ⟨1, (1 : Fin 2) >> encM L1, (0 : Fin 2) >> encM R1⟩⟩ := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  executeWithin 1
  finishWithin

/-- Reconstruct the upstream symbolic halting chain from the extracted
    checkpoint computations, without importing its unrelated 18 halting
    certificates. -/
theorem blankF424_is_halt : IsHalt target_tm := by
  have hPrefix : (init ([] : List (Fin 2))) [target_tm]⊢*
      (evalSym target_tm initSymCyc3_F424) := by
    exact ⟨18 + costIterM424 19217 startF424M,
      blankToInitSymCyc3_exact_reaches⟩
  have hc1 : (evalSym target_tm initSymCyc3_F424) [target_tm]⊢* (evalSym target_tm symChk4096_F424) := by
    rw [← sym_chk1_F424]
    exact stepSym4096_sound initSymCyc3_F424
  have hc2 : (evalSym target_tm symChk4096_F424) [target_tm]⊢* (evalSym target_tm symChk8192_F424) := by
    rw [← sym_chk2_F424]
    exact stepSym4096_sound symChk4096_F424
  have hc3 : (evalSym target_tm symChk8192_F424) [target_tm]⊢* (evalSym target_tm symChk12288_F424) := by
    rw [← sym_chk3_F424]
    exact stepSym4096_sound symChk8192_F424
  have hc4 : (evalSym target_tm symChk12288_F424) [target_tm]⊢* (evalSym target_tm symChk16384_F424) := by
    rw [← sym_chk4_F424]
    exact stepSym4096_sound symChk12288_F424
  have hc5 : (evalSym target_tm symChk16384_F424) [target_tm]⊢* (evalSym target_tm symChk20480_F424) := by
    rw [← sym_chk5_F424]
    exact stepSym4096_sound symChk16384_F424
  have hc6 : (evalSym target_tm symChk20480_F424) [target_tm]⊢* (evalSym target_tm symChk24576_F424) := by
    rw [← sym_chk6_F424]
    exact stepSym4096_sound symChk20480_F424
  have hc7 : (evalSym target_tm symChk24576_F424) [target_tm]⊢* (evalSym target_tm symChk28672_F424) := by
    rw [← sym_chk7_F424]
    exact stepSym4096_sound symChk24576_F424
  have hc8 : (evalSym target_tm symChk28672_F424) [target_tm]⊢* (evalSym target_tm symChk32768_F424) := by
    rw [← sym_chk8_F424]
    exact stepSym4096_sound symChk28672_F424
  have hc9 : (evalSym target_tm symChk32768_F424) [target_tm]⊢* (evalSym target_tm symChk36864_F424) := by
    rw [← sym_chk9_F424]
    exact stepSym4096_sound symChk32768_F424
  have hc10 : (evalSym target_tm symChk36864_F424) [target_tm]⊢* (evalSym target_tm symChk40960_F424) := by
    rw [← sym_chk10_F424]
    exact stepSym4096_sound symChk36864_F424
  have hc11 : (evalSym target_tm symChk40960_F424) [target_tm]⊢* (evalSym target_tm symChk45056_F424) := by
    rw [← sym_chk11_F424]
    exact stepSym4096_sound symChk40960_F424
  have hc12 : (evalSym target_tm symChk45056_F424) [target_tm]⊢* (evalSym target_tm symChk49152_F424) := by
    rw [← sym_chk12_F424]
    exact stepSym4096_sound symChk45056_F424
  have hc13 : (evalSym target_tm symChk49152_F424) [target_tm]⊢* (evalSym target_tm symChk53248_F424) := by
    rw [← sym_chk13_F424]
    exact stepSym4096_sound symChk49152_F424
  have hc14 : (evalSym target_tm symChk53248_F424) [target_tm]⊢* (evalSym target_tm symChk57344_F424) := by
    rw [← sym_chk14_F424]
    exact stepSym4096_sound symChk53248_F424
  have hc15 : (evalSym target_tm symChk57344_F424) [target_tm]⊢* (evalSym target_tm symChk61440_F424) := by
    rw [← sym_chk15_F424]
    exact stepSym4096_sound symChk57344_F424
  have hc16 : (evalSym target_tm symChk61440_F424) [target_tm]⊢* (evalSym target_tm symChk65536_F424) := by
    rw [← sym_chk16_F424]
    exact stepSym4096_sound symChk61440_F424
  have hc17 : (evalSym target_tm symChk65536_F424) [target_tm]⊢* (evalSym target_tm symChk69632_F424) := by
    rw [← sym_chk17_F424]
    exact stepSym4096_sound symChk65536_F424
  have hc18 : (evalSym target_tm symChk69632_F424) [target_tm]⊢* (evalSym target_tm symChk70511_F424) := by
    rw [← sym_chk18_F424]
    exact stepStar_trans (iterStep_sound stepSym256 (evalSym target_tm)
        (stepSym256_sound (target_tm := target_tm)) 3 symChk69632_F424)
      (stepStar_trans (iterStep_sound stepSym16 (evalSym target_tm)
        (stepSym16_sound (target_tm := target_tm)) 6 _)
        (iterStep_sound stepSym (evalSym target_tm)
          (stepSym_sound (target_tm := target_tm)) 15 _))
  have hTrace : (evalSym target_tm initSymCyc3_F424) [target_tm]⊢* (evalSym target_tm symChk70511_F424) := by
    exact stepStar_trans hc1 (stepStar_trans hc2 (stepStar_trans hc3 (stepStar_trans hc4 (stepStar_trans hc5 (stepStar_trans hc6 (stepStar_trans hc7 (stepStar_trans hc8 (stepStar_trans hc9 (stepStar_trans hc10 (stepStar_trans hc11 (stepStar_trans hc12 (stepStar_trans hc13 (stepStar_trans hc14 (stepStar_trans hc15 (stepStar_trans hc16 (stepStar_trans hc17 (stepStar_trans hc18 (hc18))))))))))))))))))
  have h_to_halt_sym : (init ([] : List (Fin 2))) [target_tm]⊢*
      (evalSym target_tm symChk70511_F424) :=
    stepStar_trans hPrefix hTrace
  have h_final := step_DL_zero_halt_F424
    (encSymL symChk70511_F424.2.1.tail)
    (encSymR symChk70511_F424.2.2.tail)
  exact ⟨_, stepStar_trans h_to_halt_sym (stepPlus_stepStar h_final), rfl⟩

#print axioms blankF424_is_halt
#print axioms step_DL_zero_halt_F424_exact


end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
