import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M057
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_13 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,4,4⟩ (.node .empty ⟨0,false,4,11⟩ .empty)) ⟨0,false,4,21⟩ (.node (.node .empty ⟨0,false,4,23⟩ .empty) ⟨0,false,10,9⟩ .empty)) ⟨0,false,10,19⟩ (.node (.node (.node .empty ⟨0,false,10,21⟩ .empty) ⟨0,false,10,23⟩ (.node .empty ⟨0,false,10,27⟩ .empty)) ⟨0,false,10,30⟩ (.node (.node .empty ⟨0,false,16,13⟩ .empty) ⟨0,false,16,19⟩ .empty)))
def t14_27 : Tree := (.node (.node (.node (.node .empty ⟨0,false,16,23⟩ .empty) ⟨0,false,16,27⟩ (.node .empty ⟨0,false,24,0⟩ .empty)) ⟨0,false,25,11⟩ (.node (.node .empty ⟨0,false,25,19⟩ .empty) ⟨0,false,25,21⟩ .empty)) ⟨0,false,25,23⟩ (.node (.node (.node .empty ⟨0,false,25,27⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,5,3⟩ .empty)) ⟨1,false,5,18⟩ (.node (.node .empty ⟨1,false,5,26⟩ .empty) ⟨1,false,7,16⟩ .empty)))
def t0_27 : Tree := .node t0_13 ⟨0,false,16,21⟩ t14_27
def t28_41 : Tree := (.node (.node (.node (.node .empty ⟨1,false,7,26⟩ .empty) ⟨1,false,7,33⟩ (.node .empty ⟨1,false,7,39⟩ .empty)) ⟨1,false,9,0⟩ (.node (.node .empty ⟨1,false,11,8⟩ .empty) ⟨1,false,11,18⟩ .empty)) ⟨1,false,11,26⟩ (.node (.node (.node .empty ⟨1,false,13,5⟩ .empty) ⟨1,false,13,16⟩ (.node .empty ⟨1,false,13,24⟩ .empty)) ⟨1,false,13,26⟩ (.node (.node .empty ⟨1,false,13,33⟩ .empty) ⟨1,false,13,39⟩ .empty)))
def t42_55 : Tree := (.node (.node (.node (.node .empty ⟨1,false,15,24⟩ .empty) ⟨1,false,15,26⟩ (.node .empty ⟨1,false,15,33⟩ .empty)) ⟨1,false,15,36⟩ (.node (.node .empty ⟨1,false,15,37⟩ .empty) ⟨1,false,17,18⟩ .empty)) ⟨1,false,17,26⟩ (.node (.node (.node .empty ⟨1,false,19,16⟩ .empty) ⟨1,false,19,24⟩ (.node .empty ⟨1,false,19,26⟩ .empty)) ⟨1,false,19,33⟩ (.node (.node .empty ⟨1,false,19,39⟩ .empty) ⟨1,false,21,10⟩ .empty)))
def t28_55 : Tree := .node t28_41 ⟨1,false,15,10⟩ t42_55
def t0_55 : Tree := .node t0_27 ⟨1,false,7,24⟩ t28_55
def t56_69 : Tree := (.node (.node (.node (.node .empty ⟨1,false,21,26⟩ .empty) ⟨1,false,21,33⟩ (.node .empty ⟨1,false,21,36⟩ .empty)) ⟨1,false,21,37⟩ (.node (.node .empty ⟨1,false,23,3⟩ .empty) ⟨1,false,26,10⟩ .empty)) ⟨1,false,26,18⟩ (.node (.node (.node .empty ⟨1,false,26,24⟩ .empty) ⟨1,false,26,26⟩ (.node .empty ⟨1,false,26,33⟩ .empty)) ⟨1,false,26,36⟩ (.node (.node .empty ⟨1,false,28,3⟩ .empty) ⟨1,false,33,10⟩ .empty)))
def t70_83 : Tree := (.node (.node (.node (.node .empty ⟨1,false,33,24⟩ .empty) ⟨1,false,33,26⟩ (.node .empty ⟨1,false,33,33⟩ .empty)) ⟨1,false,33,36⟩ (.node (.node .empty ⟨1,false,35,10⟩ .empty) ⟨1,false,35,16⟩ .empty)) ⟨1,false,35,24⟩ (.node (.node (.node .empty ⟨1,false,35,26⟩ .empty) ⟨1,false,35,33⟩ (.node .empty ⟨1,false,35,36⟩ .empty)) ⟨1,false,35,39⟩ (.node (.node .empty ⟨1,false,36,10⟩ .empty) ⟨1,false,36,16⟩ .empty)))
def t56_83 : Tree := .node t56_69 ⟨1,false,33,18⟩ t70_83
def t84_97 : Tree := (.node (.node (.node (.node .empty ⟨1,false,36,26⟩ .empty) ⟨1,false,36,33⟩ (.node .empty ⟨1,false,36,36⟩ .empty)) ⟨1,false,36,39⟩ (.node (.node .empty ⟨1,true,1,5⟩ .empty) ⟨1,true,1,12⟩ .empty)) ⟨1,true,1,22⟩ (.node (.node (.node .empty ⟨1,true,5,10⟩ .empty) ⟨1,true,5,20⟩ (.node .empty ⟨1,true,5,22⟩ .empty)) ⟨1,true,5,28⟩ (.node (.node .empty ⟨1,true,5,31⟩ .empty) ⟨1,true,11,20⟩ .empty)))
def t98_110 : Tree := (.node (.node (.node (.node .empty ⟨1,true,11,28⟩ .empty) ⟨1,true,11,29⟩ (.node .empty ⟨1,true,17,12⟩ .empty)) ⟨1,true,17,20⟩ (.node (.node .empty ⟨1,true,17,22⟩ .empty) ⟨1,true,17,28⟩ .empty)) ⟨1,true,23,0⟩ (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,6,1⟩ .empty) ⟨2,false,8,6⟩ (.node (.node .empty ⟨2,false,8,14⟩ .empty) ⟨2,false,8,34⟩ .empty)))
def t84_110 : Tree := .node t84_97 ⟨1,true,11,22⟩ t98_110
def t56_110 : Tree := .node t56_83 ⟨1,false,36,24⟩ t84_110
def t0_110 : Tree := .node t0_55 ⟨1,false,21,24⟩ t56_110
def t111_124 : Tree := (.node (.node (.node (.node .empty ⟨2,false,14,6⟩ .empty) ⟨2,false,14,14⟩ (.node .empty ⟨2,false,14,34⟩ .empty)) ⟨2,false,20,6⟩ (.node (.node .empty ⟨2,false,20,14⟩ .empty) ⟨2,false,20,34⟩ .empty)) ⟨2,false,22,6⟩ (.node (.node (.node .empty ⟨2,false,22,7⟩ .empty) ⟨2,false,22,9⟩ (.node .empty ⟨2,false,22,34⟩ .empty)) ⟨2,false,27,6⟩ (.node (.node .empty ⟨2,false,27,7⟩ .empty) ⟨2,false,27,9⟩ .empty)))
def t125_138 : Tree := (.node (.node (.node (.node .empty ⟨2,false,29,1⟩ .empty) ⟨2,false,32,6⟩ (.node .empty ⟨2,false,32,7⟩ .empty)) ⟨2,false,32,9⟩ (.node (.node .empty ⟨2,false,32,34⟩ .empty) ⟨2,false,34,6⟩ .empty)) ⟨2,false,34,7⟩ (.node (.node (.node .empty ⟨2,false,34,9⟩ .empty) ⟨2,false,34,34⟩ (.node .empty ⟨2,false,37,6⟩ .empty)) ⟨2,false,37,7⟩ (.node (.node .empty ⟨2,false,37,9⟩ .empty) ⟨2,false,37,14⟩ .empty)))
def t111_138 : Tree := .node t111_124 ⟨2,false,27,34⟩ t125_138
def t139_152 : Tree := (.node (.node (.node (.node .empty ⟨2,false,38,6⟩ .empty) ⟨2,false,38,7⟩ (.node .empty ⟨2,false,38,9⟩ .empty)) ⟨2,false,38,14⟩ (.node (.node .empty ⟨2,false,38,34⟩ .empty) ⟨2,true,6,17⟩ .empty)) ⟨2,true,6,25⟩ (.node (.node (.node .empty ⟨2,true,6,27⟩ .empty) ⟨2,true,8,25⟩ (.node .empty ⟨2,true,8,27⟩ .empty)) ⟨2,true,8,32⟩ (.node (.node .empty ⟨2,true,8,38⟩ .empty) ⟨2,true,12,7⟩ .empty)))
def t153_165 : Tree := (.node (.node (.node (.node .empty ⟨2,true,12,25⟩ .empty) ⟨2,true,12,27⟩ (.node .empty ⟨2,true,14,25⟩ .empty)) ⟨2,true,14,27⟩ (.node (.node .empty ⟨2,true,14,32⟩ .empty) ⟨2,true,14,38⟩ .empty)) ⟨2,true,18,17⟩ (.node (.node (.node .empty ⟨2,true,18,25⟩ .empty) ⟨2,true,18,27⟩ .empty) ⟨2,true,20,25⟩ (.node (.node .empty ⟨2,true,20,27⟩ .empty) ⟨2,true,20,32⟩ .empty)))
def t139_165 : Tree := .node t139_152 ⟨2,true,12,17⟩ t153_165
def t111_165 : Tree := .node t111_138 ⟨2,false,37,34⟩ t139_165
def t166_179 : Tree := (.node (.node (.node (.node .empty ⟨2,true,22,19⟩ .empty) ⟨2,true,22,25⟩ (.node .empty ⟨2,true,22,27⟩ .empty)) ⟨2,true,22,32⟩ (.node (.node .empty ⟨2,true,27,17⟩ .empty) ⟨2,true,27,25⟩ .empty)) ⟨2,true,27,27⟩ (.node (.node (.node .empty ⟨2,true,27,32⟩ .empty) ⟨2,true,32,19⟩ (.node .empty ⟨2,true,32,25⟩ .empty)) ⟨2,true,32,27⟩ (.node (.node .empty ⟨2,true,32,32⟩ .empty) ⟨2,true,34,17⟩ .empty)))
def t180_193 : Tree := (.node (.node (.node (.node .empty ⟨2,true,34,27⟩ .empty) ⟨2,true,34,32⟩ (.node .empty ⟨2,true,37,25⟩ .empty)) ⟨2,true,37,27⟩ (.node (.node .empty ⟨2,true,37,32⟩ .empty) ⟨2,true,37,38⟩ .empty)) ⟨2,true,38,25⟩ (.node (.node (.node .empty ⟨2,true,38,27⟩ .empty) ⟨2,true,38,32⟩ (.node .empty ⟨2,true,38,38⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,8,6⟩ .empty)))
def t166_193 : Tree := .node t166_179 ⟨2,true,34,25⟩ t180_193
def t194_207 : Tree := (.node (.node (.node (.node .empty ⟨3,false,14,6⟩ .empty) ⟨3,false,14,14⟩ (.node .empty ⟨3,false,14,34⟩ .empty)) ⟨3,false,15,3⟩ (.node (.node .empty ⟨3,false,15,5⟩ .empty) ⟨3,false,15,8⟩ .empty)) ⟨3,false,20,6⟩ (.node (.node (.node .empty ⟨3,false,20,34⟩ .empty) ⟨3,false,21,5⟩ (.node .empty ⟨3,false,21,8⟩ .empty)) ⟨3,false,22,6⟩ (.node (.node .empty ⟨3,false,22,34⟩ .empty) ⟨3,false,26,5⟩ .empty)))
def t208_220 : Tree := (.node (.node (.node (.node .empty ⟨3,false,27,6⟩ .empty) ⟨3,false,27,34⟩ (.node .empty ⟨3,false,32,6⟩ .empty)) ⟨3,false,32,34⟩ (.node (.node .empty ⟨3,false,33,5⟩ .empty) ⟨3,false,33,8⟩ .empty)) ⟨3,false,34,6⟩ (.node (.node (.node .empty ⟨3,false,34,34⟩ .empty) ⟨3,false,35,5⟩ .empty) ⟨3,false,35,8⟩ (.node (.node .empty ⟨3,false,36,5⟩ .empty) ⟨3,false,36,8⟩ .empty)))
def t194_220 : Tree := .node t194_207 ⟨3,false,26,8⟩ t208_220
def t166_220 : Tree := .node t166_193 ⟨3,false,8,34⟩ t194_220
def t111_220 : Tree := .node t111_165 ⟨2,true,20,38⟩ t166_220
def t0_220 : Tree := .node t0_110 ⟨2,false,14,4⟩ t111_220
def t221_234 : Tree := (.node (.node (.node (.node .empty ⟨3,false,37,34⟩ .empty) ⟨3,false,38,6⟩ (.node .empty ⟨3,false,38,14⟩ .empty)) ⟨3,false,38,34⟩ (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,7,0⟩ .empty)) ⟨3,true,7,35⟩ (.node (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,13,15⟩ (.node .empty ⟨3,true,13,35⟩ .empty)) ⟨3,true,15,3⟩ (.node (.node .empty ⟨3,true,15,5⟩ .empty) ⟨3,true,15,8⟩ .empty)))
def t235_248 : Tree := (.node (.node (.node (.node .empty ⟨3,true,19,35⟩ .empty) ⟨3,true,21,3⟩ (.node .empty ⟨3,true,21,5⟩ .empty)) ⟨3,true,21,8⟩ (.node (.node .empty ⟨3,true,21,35⟩ .empty) ⟨3,true,26,5⟩ .empty)) ⟨3,true,26,8⟩ (.node (.node (.node .empty ⟨3,true,26,35⟩ .empty) ⟨3,true,30,0⟩ (.node .empty ⟨3,true,33,5⟩ .empty)) ⟨3,true,33,8⟩ (.node (.node .empty ⟨3,true,33,35⟩ .empty) ⟨3,true,35,5⟩ .empty)))
def t221_248 : Tree := .node t221_234 ⟨3,true,15,35⟩ t235_248
def t249_262 : Tree := (.node (.node (.node (.node .empty ⟨3,true,35,15⟩ .empty) ⟨3,true,35,35⟩ (.node .empty ⟨3,true,36,5⟩ .empty)) ⟨3,true,36,8⟩ (.node (.node .empty ⟨3,true,36,35⟩ .empty) ⟨4,false,0,6⟩ .empty)) ⟨4,false,0,13⟩ (.node (.node (.node .empty ⟨4,false,0,23⟩ .empty) ⟨4,false,8,0⟩ (.node .empty ⟨4,false,22,1⟩ .empty)) ⟨4,false,22,4⟩ (.node (.node .empty ⟨4,false,27,4⟩ .empty) ⟨4,false,31,0⟩ .empty)))
def t263_276 : Tree := (.node (.node (.node (.node .empty ⟨4,false,32,4⟩ .empty) ⟨4,false,34,4⟩ (.node .empty ⟨4,false,37,4⟩ .empty)) ⟨4,false,38,4⟩ (.node (.node .empty ⟨4,true,0,11⟩ .empty) ⟨4,true,0,21⟩ .empty)) ⟨4,true,0,23⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,4,21⟩ (.node .empty ⟨4,true,4,23⟩ .empty)) ⟨4,true,4,30⟩ (.node (.node .empty ⟨4,true,5,8⟩ .empty) ⟨4,true,5,26⟩ .empty)))
def t249_276 : Tree := .node t249_262 ⟨4,false,32,1⟩ t263_276
def t221_276 : Tree := .node t221_248 ⟨3,true,35,8⟩ t249_276
def t277_290 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,33⟩ .empty) ⟨4,true,8,6⟩ (.node .empty ⟨4,true,8,34⟩ .empty)) ⟨4,true,10,13⟩ (.node (.node .empty ⟨4,true,10,21⟩ .empty) ⟨4,true,10,23⟩ .empty)) ⟨4,true,11,18⟩ (.node (.node (.node .empty ⟨4,true,11,26⟩ .empty) ⟨4,true,13,26⟩ (.node .empty ⟨4,true,13,33⟩ .empty)) ⟨4,true,13,39⟩ (.node (.node .empty ⟨4,true,14,6⟩ .empty) ⟨4,true,14,14⟩ .empty)))
def t291_304 : Tree := (.node (.node (.node (.node .empty ⟨4,true,15,26⟩ .empty) ⟨4,true,15,33⟩ (.node .empty ⟨4,true,15,37⟩ .empty)) ⟨4,true,16,11⟩ (.node (.node .empty ⟨4,true,16,21⟩ .empty) ⟨4,true,16,23⟩ .empty)) ⟨4,true,17,26⟩ (.node (.node (.node .empty ⟨4,true,19,26⟩ .empty) ⟨4,true,19,33⟩ (.node .empty ⟨4,true,20,6⟩ .empty)) ⟨4,true,20,34⟩ (.node (.node .empty ⟨4,true,21,26⟩ .empty) ⟨4,true,21,33⟩ .empty)))
def t277_304 : Tree := .node t277_290 ⟨4,true,14,34⟩ t291_304
def t305_318 : Tree := (.node (.node (.node (.node .empty ⟨4,true,22,7⟩ .empty) ⟨4,true,22,34⟩ (.node .empty ⟨4,true,23,8⟩ .empty)) ⟨4,true,25,21⟩ (.node (.node .empty ⟨4,true,25,23⟩ .empty) ⟨4,true,25,30⟩ .empty)) ⟨4,true,26,26⟩ (.node (.node (.node .empty ⟨4,true,26,33⟩ .empty) ⟨4,true,27,6⟩ (.node .empty ⟨4,true,27,7⟩ .empty)) ⟨4,true,27,34⟩ (.node (.node .empty ⟨4,true,28,8⟩ .empty) ⟨4,true,32,6⟩ .empty)))
def t319_331 : Tree := (.node (.node (.node (.node .empty ⟨4,true,32,34⟩ .empty) ⟨4,true,33,18⟩ (.node .empty ⟨4,true,33,26⟩ .empty)) ⟨4,true,33,33⟩ (.node (.node .empty ⟨4,true,34,6⟩ .empty) ⟨4,true,34,7⟩ .empty)) ⟨4,true,34,34⟩ (.node (.node (.node .empty ⟨4,true,35,26⟩ .empty) ⟨4,true,35,33⟩ .empty) ⟨4,true,35,39⟩ (.node (.node .empty ⟨4,true,36,26⟩ .empty) ⟨4,true,36,33⟩ .empty)))
def t305_331 : Tree := .node t305_318 ⟨4,true,32,7⟩ t319_331
def t277_331 : Tree := .node t277_304 ⟨4,true,22,6⟩ t305_331
def t221_331 : Tree := .node t221_276 ⟨4,true,7,26⟩ t277_331
def t332_345 : Tree := (.node (.node (.node (.node .empty ⟨4,true,37,7⟩ .empty) ⟨4,true,37,34⟩ (.node .empty ⟨4,true,38,6⟩ .empty)) ⟨4,true,38,7⟩ (.node (.node .empty ⟨4,true,38,14⟩ .empty) ⟨4,true,38,34⟩ .empty)) ⟨5,false,0,5⟩ (.node (.node (.node .empty ⟨5,false,0,12⟩ .empty) ⟨5,false,0,22⟩ (.node .empty ⟨5,false,1,10⟩ .empty)) ⟨5,false,1,22⟩ (.node (.node .empty ⟨5,false,1,28⟩ .empty) ⟨5,false,1,31⟩ .empty)))
def t346_359 : Tree := (.node (.node (.node (.node .empty ⟨5,false,5,22⟩ .empty) ⟨5,false,5,28⟩ (.node .empty ⟨5,false,5,29⟩ .empty)) ⟨5,false,6,7⟩ (.node (.node .empty ⟨5,false,6,25⟩ .empty) ⟨5,false,6,27⟩ .empty)) ⟨5,false,8,25⟩ (.node (.node (.node .empty ⟨5,false,8,27⟩ .empty) ⟨5,false,8,32⟩ (.node .empty ⟨5,false,11,12⟩ .empty)) ⟨5,false,11,22⟩ (.node (.node .empty ⟨5,false,11,28⟩ .empty) ⟨5,false,12,17⟩ .empty)))
def t332_359 : Tree := .node t332_345 ⟨5,false,5,20⟩ t346_359
def t360_373 : Tree := (.node (.node (.node (.node .empty ⟨5,false,12,27⟩ .empty) ⟨5,false,14,25⟩ (.node .empty ⟨5,false,14,27⟩ .empty)) ⟨5,false,14,32⟩ (.node (.node .empty ⟨5,false,14,38⟩ .empty) ⟨5,false,17,10⟩ .empty)) ⟨5,false,17,22⟩ (.node (.node (.node .empty ⟨5,false,17,28⟩ .empty) ⟨5,false,17,31⟩ (.node .empty ⟨5,false,18,25⟩ .empty)) ⟨5,false,18,27⟩ (.node (.node .empty ⟨5,false,20,25⟩ .empty) ⟨5,false,20,27⟩ .empty)))
def t374_386 : Tree := (.node (.node (.node (.node .empty ⟨5,false,22,25⟩ .empty) ⟨5,false,22,27⟩ (.node .empty ⟨5,false,22,32⟩ .empty)) ⟨5,false,23,5⟩ (.node (.node .empty ⟨5,false,27,25⟩ .empty) ⟨5,false,27,27⟩ .empty)) ⟨5,false,27,32⟩ (.node (.node (.node .empty ⟨5,false,29,7⟩ .empty) ⟨5,false,32,19⟩ .empty) ⟨5,false,32,25⟩ (.node (.node .empty ⟨5,false,32,27⟩ .empty) ⟨5,false,32,32⟩ .empty)))
def t360_386 : Tree := .node t360_373 ⟨5,false,20,32⟩ t374_386
def t332_386 : Tree := .node t332_359 ⟨5,false,12,25⟩ t360_386
def t387_400 : Tree := (.node (.node (.node (.node .empty ⟨5,false,34,25⟩ .empty) ⟨5,false,34,27⟩ (.node .empty ⟨5,false,34,32⟩ .empty)) ⟨5,false,37,25⟩ (.node (.node .empty ⟨5,false,37,27⟩ .empty) ⟨5,false,37,32⟩ .empty)) ⟨5,false,38,25⟩ (.node (.node (.node .empty ⟨5,false,38,27⟩ .empty) ⟨5,false,38,32⟩ (.node .empty ⟨5,false,38,38⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,4,9⟩ .empty)))
def t401_414 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,5⟩ .empty) ⟨5,true,7,24⟩ (.node .empty ⟨5,true,8,4⟩ .empty)) ⟨5,true,9,3⟩ (.node (.node .empty ⟨5,true,10,19⟩ .empty) ⟨5,true,10,27⟩ .empty)) ⟨5,true,13,16⟩ (.node (.node (.node .empty ⟨5,true,13,24⟩ .empty) ⟨5,true,15,10⟩ (.node .empty ⟨5,true,15,24⟩ .empty)) ⟨5,true,15,36⟩ (.node (.node .empty ⟨5,true,16,27⟩ .empty) ⟨5,true,19,24⟩ .empty)))
def t387_414 : Tree := .node t387_400 ⟨5,true,4,27⟩ t401_414
def t415_428 : Tree := (.node (.node (.node (.node .empty ⟨5,true,21,24⟩ .empty) ⟨5,true,21,36⟩ (.node .empty ⟨5,true,22,9⟩ .empty)) ⟨5,true,24,4⟩ (.node (.node .empty ⟨5,true,25,9⟩ .empty) ⟨5,true,25,27⟩ .empty)) ⟨5,true,26,10⟩ (.node (.node (.node .empty ⟨5,true,26,24⟩ .empty) ⟨5,true,26,36⟩ (.node .empty ⟨5,true,27,9⟩ .empty)) ⟨5,true,30,5⟩ (.node (.node .empty ⟨5,true,31,4⟩ .empty) ⟨5,true,32,9⟩ .empty)))
def t429_441 : Tree := (.node (.node (.node (.node .empty ⟨5,true,33,24⟩ .empty) ⟨5,true,33,36⟩ (.node .empty ⟨5,true,34,9⟩ .empty)) ⟨5,true,35,10⟩ (.node (.node .empty ⟨5,true,35,16⟩ .empty) ⟨5,true,35,24⟩ .empty)) ⟨5,true,35,36⟩ (.node (.node (.node .empty ⟨5,true,36,10⟩ .empty) ⟨5,true,36,24⟩ .empty) ⟨5,true,36,36⟩ (.node (.node .empty ⟨5,true,37,9⟩ .empty) ⟨5,true,38,9⟩ .empty)))
def t415_441 : Tree := .node t415_428 ⟨5,true,33,10⟩ t429_441
def t387_441 : Tree := .node t387_414 ⟨5,true,21,10⟩ t415_441
def t332_441 : Tree := .node t332_386 ⟨5,false,34,17⟩ t387_441
def t221_441 : Tree := .node t221_331 ⟨4,true,37,6⟩ t332_441
def t0_441 : Tree := .node t0_220 ⟨3,false,37,6⟩ t221_441
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 10, 6, 7, 0, 0, 8, 21, 9, 0, 2, 0, 11, 16, 12, 13, 0, 0, 14, 15, 0, 0, 32, 0, 17, 25, 18, 19, 0, 0, 20, 21, 0, 0, 22, 26, 23, 24, 29, 0, 9, 0, 5, 0, 27, 36, 28, 0, 29, 30, 0, 0, 31, 0, 9, 33, 23, 0, 34, 35, 28, 0, 38, 0, 37, 21, 28, 15, 28],#[0, 1, 3, 2, 0, 0, 4, 14, 5, 0, 7, 6, 24, 35, 36, 8, 9, 34, 10, 0, 32, 11, 12, 0, 0, 13, 29, 0, 16, 15, 0, 0, 17, 0, 0, 18, 19, 0, 20, 37, 0, 21, 22, 0, 0, 23, 22, 0, 25, 0, 0, 26, 27, 0, 28, 26, 0, 21, 0, 30, 31, 0, 0, 11, 0, 33, 25, 0, 24, 35, 0, 0, 32, 0, 38, 0, 0, 39, 17, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,9)],[(false,2)],[(false,1)],[(true,4),(true,25)],[(true,5)],[(false,6)],[(true,7)],[(true,8),(true,24),(true,31)],[(false,5)],[(true,10)],[(true,11)],[(false,12)],[(true,13)],[(false,14),(false,38)],[(false,11)],[(true,16)],[(true,17)],[(false,18)],[(true,19)],[(false,8),(false,20),(false,37)],[(true,21)],[(true,22),(true,32)],[(false,23)],[(false,17)],[(false,22)],[(true,26)],[(true,27),(true,34),(true,37),(true,38)],[(true,23),(true,28)],[(false,29)],[(true,30)],[(true,15)],[(false,32)],[(true,33)],[(false,34)],[(false,27)],[(true,36)],[(true,35)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,5)],[(false,5)],[(true,7)],[(false,8)],[(false,9)],[(true,10),(true,31)],[(false,11)],[(true,12)],[(true,3)],[(true,14)],[(false,14)],[(false,16),(false,39)],[(true,17)],[(false,18)],[(false,19)],[(true,20),(true,28)],[(false,21),(false,23)],[(true,22)],[(false,6),(false,34)],[(false,24),(false,33)],[(true,25),(true,27)],[(false,26)],[(false,27)],[(false,13)],[(true,29)],[(false,30)],[(false,10),(false,36)],[(true,32)],[(true,8)],[(true,6),(true,34)],[(false,7)],[(true,19)],[(false,37)],[(true,38)]],
  t0_441⟩
theorem check0_13 : t0_13.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check14_27 : t14_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node13 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,16,21⟩ = true := by decide
theorem check0_27 : t0_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node13 check0_13 check14_27
theorem check28_41 : t28_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check42_55 : t42_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node41 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,15,10⟩ = true := by decide
theorem check28_55 : t28_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node41 check28_41 check42_55
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,7,24⟩ = true := by decide
theorem check0_55 : t0_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check0_27 check28_55
theorem check56_69 : t56_69.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check70_83 : t70_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node69 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,33,18⟩ = true := by decide
theorem check56_83 : t56_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node69 check56_69 check70_83
theorem check84_97 : t84_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check98_110 : t98_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,11,22⟩ = true := by decide
theorem check84_110 : t84_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check84_97 check98_110
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,36,24⟩ = true := by decide
theorem check56_110 : t56_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check56_83 check84_110
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,21,24⟩ = true := by decide
theorem check0_110 : t0_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check0_55 check56_110
theorem check111_124 : t111_124.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check125_138 : t125_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node124 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,27,34⟩ = true := by decide
theorem check111_138 : t111_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node124 check111_124 check125_138
theorem check139_152 : t139_152.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check153_165 : t153_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node152 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,12,17⟩ = true := by decide
theorem check139_165 : t139_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node152 check139_152 check153_165
theorem node138 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,37,34⟩ = true := by decide
theorem check111_165 : t111_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node138 check111_138 check139_165
theorem check166_179 : t166_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check180_193 : t180_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,34,25⟩ = true := by decide
theorem check166_193 : t166_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check166_179 check180_193
theorem check194_207 : t194_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check208_220 : t208_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node207 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,26,8⟩ = true := by decide
theorem check194_220 : t194_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node207 check194_207 check208_220
theorem node193 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,34⟩ = true := by decide
theorem check166_220 : t166_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node193 check166_193 check194_220
theorem node165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,20,38⟩ = true := by decide
theorem check111_220 : t111_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node165 check111_165 check166_220
theorem node110 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,14,4⟩ = true := by decide
theorem check0_220 : t0_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node110 check0_110 check111_220
theorem check221_234 : t221_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check235_248 : t235_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node234 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,15,35⟩ = true := by decide
theorem check221_248 : t221_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node234 check221_234 check235_248
theorem check249_262 : t249_262.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check263_276 : t263_276.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node262 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,32,1⟩ = true := by decide
theorem check249_276 : t249_276.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node262 check249_262 check263_276
theorem node248 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,35,8⟩ = true := by decide
theorem check221_276 : t221_276.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node248 check221_248 check249_276
theorem check277_290 : t277_290.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check291_304 : t291_304.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node290 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,14,34⟩ = true := by decide
theorem check277_304 : t277_304.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node290 check277_290 check291_304
theorem check305_318 : t305_318.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check319_331 : t319_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node318 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,32,7⟩ = true := by decide
theorem check305_331 : t305_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node318 check305_318 check319_331
theorem node304 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,22,6⟩ = true := by decide
theorem check277_331 : t277_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node304 check277_304 check305_331
theorem node276 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,26⟩ = true := by decide
theorem check221_331 : t221_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node276 check221_276 check277_331
theorem check332_345 : t332_345.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check346_359 : t346_359.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node345 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,5,20⟩ = true := by decide
theorem check332_359 : t332_359.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node345 check332_345 check346_359
theorem check360_373 : t360_373.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check374_386 : t374_386.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node373 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,20,32⟩ = true := by decide
theorem check360_386 : t360_386.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node373 check360_373 check374_386
theorem node359 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,12,25⟩ = true := by decide
theorem check332_386 : t332_386.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node359 check332_359 check360_386
theorem check387_400 : t387_400.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check401_414 : t401_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node400 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,27⟩ = true := by decide
theorem check387_414 : t387_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node400 check387_400 check401_414
theorem check415_428 : t415_428.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check429_441 : t429_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node428 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,33,10⟩ = true := by decide
theorem check415_441 : t415_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node428 check415_428 check429_441
theorem node414 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,21,10⟩ = true := by decide
theorem check387_441 : t387_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node414 check387_414 check415_441
theorem node386 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,34,17⟩ = true := by decide
theorem check332_441 : t332_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node386 check332_386 check387_441
theorem node331 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,37,6⟩ = true := by decide
theorem check221_441 : t221_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node331 check221_331 check332_441
theorem node220 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,37,6⟩ = true := by decide
theorem check0_441 : t0_441.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node220 check0_220 check221_441
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_441
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M057
