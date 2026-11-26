import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M029
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_13 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,8⟩ (.node .empty ⟨0,false,2,1⟩ .empty)) ⟨0,false,2,8⟩ (.node (.node .empty ⟨0,false,2,9⟩ .empty) ⟨0,false,4,0⟩ .empty)) ⟨0,false,4,4⟩ (.node (.node (.node .empty ⟨0,false,4,7⟩ .empty) ⟨0,false,4,8⟩ (.node .empty ⟨0,false,4,12⟩ .empty)) ⟨0,false,4,16⟩ (.node (.node .empty ⟨0,false,6,0⟩ .empty) ⟨0,false,7,0⟩ .empty)))
def t14_26 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,9⟩ .empty) ⟨0,false,8,0⟩ (.node .empty ⟨0,false,8,4⟩ .empty)) ⟨0,false,8,7⟩ (.node (.node .empty ⟨0,false,8,8⟩ .empty) ⟨0,false,8,12⟩ .empty)) ⟨0,false,8,16⟩ (.node (.node (.node .empty ⟨0,false,9,8⟩ .empty) ⟨0,false,12,1⟩ .empty) ⟨0,false,12,9⟩ (.node (.node .empty ⟨0,false,13,0⟩ .empty) ⟨0,false,13,4⟩ .empty)))
def t0_26 : Tree := .node t0_13 ⟨0,false,7,1⟩ t14_26
def t27_39 : Tree := (.node (.node (.node (.node .empty ⟨0,false,13,8⟩ .empty) ⟨0,false,13,12⟩ (.node .empty ⟨0,false,13,16⟩ .empty)) ⟨0,true,0,4⟩ (.node (.node .empty ⟨0,true,0,12⟩ .empty) ⟨0,true,1,4⟩ .empty)) ⟨0,true,1,12⟩ (.node (.node (.node .empty ⟨0,true,1,16⟩ .empty) ⟨0,true,2,12⟩ .empty) ⟨0,true,4,4⟩ (.node (.node .empty ⟨0,true,4,12⟩ .empty) ⟨0,true,4,16⟩ .empty)))
def t40_52 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,1⟩ .empty) ⟨0,true,6,2⟩ (.node .empty ⟨0,true,6,3⟩ .empty)) ⟨0,true,6,4⟩ (.node (.node .empty ⟨0,true,6,9⟩ .empty) ⟨0,true,6,10⟩ .empty)) ⟨0,true,6,11⟩ (.node (.node (.node .empty ⟨0,true,6,12⟩ .empty) ⟨0,true,6,14⟩ .empty) ⟨0,true,6,15⟩ (.node (.node .empty ⟨0,true,6,16⟩ .empty) ⟨0,true,7,0⟩ .empty)))
def t27_52 : Tree := .node t27_39 ⟨0,true,6,0⟩ t40_52
def t0_52 : Tree := .node t0_26 ⟨0,false,13,7⟩ t27_52
def t53_66 : Tree := (.node (.node (.node (.node .empty ⟨0,true,7,2⟩ .empty) ⟨0,true,7,3⟩ (.node .empty ⟨0,true,7,4⟩ .empty)) ⟨0,true,7,9⟩ (.node (.node .empty ⟨0,true,7,10⟩ .empty) ⟨0,true,7,11⟩ .empty)) ⟨0,true,7,14⟩ (.node (.node (.node .empty ⟨0,true,7,15⟩ .empty) ⟨0,true,8,4⟩ (.node .empty ⟨0,true,8,12⟩ .empty)) ⟨0,true,8,16⟩ (.node (.node .empty ⟨0,true,9,12⟩ .empty) ⟨0,true,10,4⟩ .empty)))
def t67_79 : Tree := (.node (.node (.node (.node .empty ⟨0,true,10,16⟩ .empty) ⟨0,true,13,4⟩ (.node .empty ⟨0,true,13,12⟩ .empty)) ⟨0,true,13,16⟩ (.node (.node .empty ⟨0,true,14,4⟩ .empty) ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,7⟩ (.node (.node (.node .empty ⟨1,false,1,13⟩ .empty) ⟨1,false,4,7⟩ .empty) ⟨1,false,4,13⟩ (.node (.node .empty ⟨1,false,7,0⟩ .empty) ⟨1,false,8,0⟩ .empty)))
def t53_79 : Tree := .node t53_66 ⟨0,true,10,12⟩ t67_79
def t80_92 : Tree := (.node (.node (.node (.node .empty ⟨1,false,9,3⟩ .empty) ⟨1,false,9,4⟩ (.node .empty ⟨1,false,9,7⟩ .empty)) ⟨1,false,9,11⟩ (.node (.node .empty ⟨1,false,9,12⟩ .empty) ⟨1,false,9,13⟩ .empty)) ⟨1,false,9,15⟩ (.node (.node (.node .empty ⟨1,false,9,16⟩ .empty) ⟨1,false,14,0⟩ .empty) ⟨1,false,14,3⟩ (.node (.node .empty ⟨1,false,14,4⟩ .empty) ⟨1,false,14,7⟩ .empty)))
def t93_105 : Tree := (.node (.node (.node (.node .empty ⟨1,false,14,12⟩ .empty) ⟨1,false,14,13⟩ (.node .empty ⟨1,false,14,15⟩ .empty)) ⟨1,false,14,16⟩ (.node (.node .empty ⟨1,false,15,0⟩ .empty) ⟨1,false,15,3⟩ .empty)) ⟨1,false,15,4⟩ (.node (.node (.node .empty ⟨1,false,15,7⟩ .empty) ⟨1,false,15,11⟩ .empty) ⟨1,false,15,12⟩ (.node (.node .empty ⟨1,false,15,13⟩ .empty) ⟨1,false,15,15⟩ .empty)))
def t80_105 : Tree := .node t80_92 ⟨1,false,14,11⟩ t93_105
def t53_105 : Tree := .node t53_79 ⟨1,false,9,0⟩ t80_105
def t0_105 : Tree := .node t0_52 ⟨0,true,7,1⟩ t53_105
def t106_119 : Tree := (.node (.node (.node (.node .empty ⟨1,true,4,0⟩ .empty) ⟨1,true,4,3⟩ (.node .empty ⟨1,true,4,11⟩ .empty)) ⟨1,true,4,15⟩ (.node (.node .empty ⟨1,true,8,0⟩ .empty) ⟨1,true,8,3⟩ .empty)) ⟨1,true,8,11⟩ (.node (.node (.node .empty ⟨1,true,8,15⟩ .empty) ⟨1,true,13,0⟩ (.node .empty ⟨1,true,13,3⟩ .empty)) ⟨1,true,13,11⟩ (.node (.node .empty ⟨1,true,13,15⟩ .empty) ⟨2,false,0,5⟩ .empty)))
def t120_132 : Tree := (.node (.node (.node (.node .empty ⟨2,false,0,18⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,2,4⟩ .empty)) ⟨2,false,2,5⟩ (.node (.node .empty ⟨2,false,2,6⟩ .empty) ⟨2,false,2,12⟩ .empty)) ⟨2,false,2,16⟩ (.node (.node (.node .empty ⟨2,false,2,18⟩ .empty) ⟨2,false,4,0⟩ .empty) ⟨2,false,4,1⟩ (.node (.node .empty ⟨2,false,4,2⟩ .empty) ⟨2,false,4,3⟩ .empty)))
def t106_132 : Tree := .node t106_119 ⟨2,false,0,6⟩ t120_132
def t133_145 : Tree := (.node (.node (.node (.node .empty ⟨2,false,4,5⟩ .empty) ⟨2,false,4,6⟩ (.node .empty ⟨2,false,4,9⟩ .empty)) ⟨2,false,4,10⟩ (.node (.node .empty ⟨2,false,4,11⟩ .empty) ⟨2,false,4,12⟩ .empty)) ⟨2,false,4,14⟩ (.node (.node (.node .empty ⟨2,false,4,15⟩ .empty) ⟨2,false,4,16⟩ .empty) ⟨2,false,4,18⟩ (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,8,1⟩ .empty)))
def t146_158 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,3⟩ .empty) ⟨2,false,8,4⟩ (.node .empty ⟨2,false,8,5⟩ .empty)) ⟨2,false,8,6⟩ (.node (.node .empty ⟨2,false,8,9⟩ .empty) ⟨2,false,8,10⟩ .empty)) ⟨2,false,8,11⟩ (.node (.node (.node .empty ⟨2,false,8,12⟩ .empty) ⟨2,false,8,14⟩ .empty) ⟨2,false,8,15⟩ (.node (.node .empty ⟨2,false,8,16⟩ .empty) ⟨2,false,8,18⟩ .empty)))
def t133_158 : Tree := .node t133_145 ⟨2,false,8,2⟩ t146_158
def t106_158 : Tree := .node t106_132 ⟨2,false,4,4⟩ t133_158
def t159_171 : Tree := (.node (.node (.node (.node .empty ⟨2,false,9,5⟩ .empty) ⟨2,false,9,6⟩ (.node .empty ⟨2,false,9,12⟩ .empty)) ⟨2,false,9,16⟩ (.node (.node .empty ⟨2,false,9,18⟩ .empty) ⟨2,false,13,0⟩ .empty)) ⟨2,false,13,1⟩ (.node (.node (.node .empty ⟨2,false,13,2⟩ .empty) ⟨2,false,13,3⟩ .empty) ⟨2,false,13,4⟩ (.node (.node .empty ⟨2,false,13,5⟩ .empty) ⟨2,false,13,6⟩ .empty)))
def t172_184 : Tree := (.node (.node (.node (.node .empty ⟨2,false,13,10⟩ .empty) ⟨2,false,13,11⟩ (.node .empty ⟨2,false,13,12⟩ .empty)) ⟨2,false,13,14⟩ (.node (.node .empty ⟨2,false,13,15⟩ .empty) ⟨2,false,13,16⟩ .empty)) ⟨2,false,13,18⟩ (.node (.node (.node .empty ⟨2,false,14,0⟩ .empty) ⟨2,true,0,5⟩ .empty) ⟨2,true,0,6⟩ (.node (.node .empty ⟨2,true,0,17⟩ .empty) ⟨2,true,1,5⟩ .empty)))
def t159_184 : Tree := .node t159_171 ⟨2,false,13,9⟩ t172_184
def t185_197 : Tree := (.node (.node (.node (.node .empty ⟨2,true,1,18⟩ .empty) ⟨2,true,2,5⟩ (.node .empty ⟨2,true,2,6⟩ .empty)) ⟨2,true,2,17⟩ (.node (.node .empty ⟨2,true,3,5⟩ .empty) ⟨2,true,3,17⟩ .empty)) ⟨2,true,4,5⟩ (.node (.node (.node .empty ⟨2,true,4,6⟩ .empty) ⟨2,true,4,18⟩ .empty) ⟨2,true,5,1⟩ (.node (.node .empty ⟨2,true,5,2⟩ .empty) ⟨2,true,5,5⟩ .empty)))
def t198_210 : Tree := (.node (.node (.node (.node .empty ⟨2,true,5,9⟩ .empty) ⟨2,true,5,10⟩ (.node .empty ⟨2,true,5,14⟩ .empty)) ⟨2,true,5,17⟩ (.node (.node .empty ⟨2,true,6,1⟩ .empty) ⟨2,true,6,2⟩ .empty)) ⟨2,true,6,5⟩ (.node (.node (.node .empty ⟨2,true,6,6⟩ .empty) ⟨2,true,6,9⟩ .empty) ⟨2,true,6,10⟩ (.node (.node .empty ⟨2,true,6,14⟩ .empty) ⟨2,true,6,18⟩ .empty)))
def t185_210 : Tree := .node t185_197 ⟨2,true,5,6⟩ t198_210
def t159_210 : Tree := .node t159_184 ⟨2,true,1,6⟩ t185_210
def t106_210 : Tree := .node t106_158 ⟨2,false,9,4⟩ t159_210
def t0_210 : Tree := .node t0_105 ⟨1,false,15,16⟩ t106_210
def t211_224 : Tree := (.node (.node (.node (.node .empty ⟨2,true,7,6⟩ .empty) ⟨2,true,7,17⟩ (.node .empty ⟨2,true,8,5⟩ .empty)) ⟨2,true,8,6⟩ (.node (.node .empty ⟨2,true,8,18⟩ .empty) ⟨2,true,9,5⟩ .empty)) ⟨2,true,9,6⟩ (.node (.node (.node .empty ⟨2,true,9,17⟩ .empty) ⟨2,true,10,6⟩ (.node .empty ⟨2,true,10,18⟩ .empty)) ⟨2,true,11,5⟩ (.node (.node .empty ⟨2,true,11,17⟩ .empty) ⟨2,true,12,5⟩ .empty)))
def t225_237 : Tree := (.node (.node (.node (.node .empty ⟨2,true,13,6⟩ .empty) ⟨2,true,13,18⟩ (.node .empty ⟨2,true,14,5⟩ .empty)) ⟨2,true,14,6⟩ (.node (.node .empty ⟨2,true,14,17⟩ .empty) ⟨2,true,15,5⟩ .empty)) ⟨2,true,15,17⟩ (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,9⟩ .empty) ⟨3,false,3,0⟩ (.node (.node .empty ⟨3,false,3,3⟩ .empty) ⟨3,false,3,11⟩ .empty)))
def t211_237 : Tree := .node t211_224 ⟨2,true,12,17⟩ t225_237
def t238_250 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,4,2⟩ (.node .empty ⟨3,false,4,9⟩ .empty)) ⟨3,false,4,10⟩ (.node (.node .empty ⟨3,false,4,14⟩ .empty) ⟨3,false,5,0⟩ .empty)) ⟨3,false,5,1⟩ (.node (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,5,3⟩ .empty) ⟨3,false,5,9⟩ (.node (.node .empty ⟨3,false,5,10⟩ .empty) ⟨3,false,5,11⟩ .empty)))
def t251_263 : Tree := (.node (.node (.node (.node .empty ⟨3,false,5,15⟩ .empty) ⟨3,false,8,1⟩ (.node .empty ⟨3,false,8,2⟩ .empty)) ⟨3,false,8,9⟩ (.node (.node .empty ⟨3,false,8,10⟩ .empty) ⟨3,false,8,14⟩ .empty)) ⟨3,false,9,9⟩ (.node (.node (.node .empty ⟨3,false,11,3⟩ .empty) ⟨3,false,11,11⟩ .empty) ⟨3,false,11,15⟩ (.node (.node .empty ⟨3,false,13,1⟩ .empty) ⟨3,false,13,2⟩ .empty)))
def t238_263 : Tree := .node t238_250 ⟨3,false,5,14⟩ t251_263
def t211_263 : Tree := .node t211_237 ⟨3,false,3,15⟩ t238_263
def t264_276 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,10⟩ .empty) ⟨3,false,13,14⟩ (.node .empty ⟨3,false,14,1⟩ .empty)) ⟨3,false,16,0⟩ (.node (.node .empty ⟨3,true,0,4⟩ .empty) ⟨3,true,0,5⟩ .empty)) ⟨3,true,0,6⟩ (.node (.node (.node .empty ⟨3,true,0,12⟩ .empty) ⟨3,true,0,17⟩ .empty) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,10⟩ .empty) ⟨3,true,2,2⟩ .empty)))
def t277_289 : Tree := (.node (.node (.node (.node .empty ⟨3,true,2,14⟩ .empty) ⟨3,true,3,4⟩ (.node .empty ⟨3,true,3,5⟩ .empty)) ⟨3,true,3,6⟩ (.node (.node .empty ⟨3,true,3,12⟩ .empty) ⟨3,true,3,17⟩ .empty)) ⟨3,true,4,10⟩ (.node (.node (.node .empty ⟨3,true,5,0⟩ .empty) ⟨3,true,5,1⟩ .empty) ⟨3,true,5,2⟩ (.node (.node .empty ⟨3,true,5,3⟩ .empty) ⟨3,true,5,4⟩ .empty)))
def t264_289 : Tree := .node t264_276 ⟨3,true,2,10⟩ t277_289
def t290_302 : Tree := (.node (.node (.node (.node .empty ⟨3,true,5,6⟩ .empty) ⟨3,true,5,9⟩ (.node .empty ⟨3,true,5,10⟩ .empty)) ⟨3,true,5,11⟩ (.node (.node .empty ⟨3,true,5,12⟩ .empty) ⟨3,true,5,14⟩ .empty)) ⟨3,true,5,15⟩ (.node (.node (.node .empty ⟨3,true,5,17⟩ .empty) ⟨3,true,7,2⟩ .empty) ⟨3,true,7,10⟩ (.node (.node .empty ⟨3,true,7,14⟩ .empty) ⟨3,true,8,2⟩ .empty)))
def t303_315 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,10⟩ .empty) ⟨3,true,9,14⟩ (.node .empty ⟨3,true,11,4⟩ .empty)) ⟨3,true,11,5⟩ (.node (.node .empty ⟨3,true,11,6⟩ .empty) ⟨3,true,11,12⟩ .empty)) ⟨3,true,11,17⟩ (.node (.node (.node .empty ⟨3,true,12,2⟩ .empty) ⟨3,true,12,10⟩ .empty) ⟨3,true,12,14⟩ (.node (.node .empty ⟨3,true,14,2⟩ .empty) ⟨3,true,14,10⟩ .empty)))
def t290_315 : Tree := .node t290_302 ⟨3,true,9,2⟩ t303_315
def t264_315 : Tree := .node t264_289 ⟨3,true,5,5⟩ t290_315
def t211_315 : Tree := .node t211_263 ⟨3,false,13,9⟩ t264_315
def t316_329 : Tree := (.node (.node (.node (.node .empty ⟨3,true,15,2⟩ .empty) ⟨3,true,15,10⟩ (.node .empty ⟨3,true,15,14⟩ .empty)) ⟨4,false,1,3⟩ (.node (.node .empty ⟨4,false,1,11⟩ .empty) ⟨4,false,5,0⟩ .empty)) ⟨4,false,5,1⟩ (.node (.node (.node .empty ⟨4,false,5,2⟩ .empty) ⟨4,false,5,9⟩ (.node .empty ⟨4,false,5,10⟩ .empty)) ⟨4,false,5,14⟩ (.node (.node .empty ⟨4,false,6,0⟩ .empty) ⟨4,false,6,1⟩ .empty)))
def t330_342 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,3⟩ .empty) ⟨4,false,6,9⟩ (.node .empty ⟨4,false,6,10⟩ .empty)) ⟨4,false,6,11⟩ (.node (.node .empty ⟨4,false,6,14⟩ .empty) ⟨4,false,10,3⟩ .empty)) ⟨4,false,10,11⟩ (.node (.node (.node .empty ⟨4,true,1,4⟩ .empty) ⟨4,true,1,5⟩ .empty) ⟨4,true,1,6⟩ (.node (.node .empty ⟨4,true,1,12⟩ .empty) ⟨4,true,1,16⟩ .empty)))
def t316_342 : Tree := .node t316_329 ⟨4,false,6,2⟩ t330_342
def t343_355 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,9⟩ (.node .empty ⟨4,true,4,1⟩ .empty)) ⟨4,true,4,2⟩ (.node (.node .empty ⟨4,true,4,9⟩ .empty) ⟨4,true,4,10⟩ .empty)) ⟨4,true,4,14⟩ (.node (.node (.node .empty ⟨4,true,6,0⟩ .empty) ⟨4,true,6,1⟩ .empty) ⟨4,true,6,2⟩ (.node (.node .empty ⟨4,true,6,3⟩ .empty) ⟨4,true,6,4⟩ .empty)))
def t356_368 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,6⟩ .empty) ⟨4,true,6,9⟩ (.node .empty ⟨4,true,6,10⟩ .empty)) ⟨4,true,6,11⟩ (.node (.node .empty ⟨4,true,6,12⟩ .empty) ⟨4,true,6,14⟩ .empty)) ⟨4,true,6,15⟩ (.node (.node (.node .empty ⟨4,true,6,16⟩ .empty) ⟨4,true,6,18⟩ .empty) ⟨4,true,8,1⟩ (.node (.node .empty ⟨4,true,8,2⟩ .empty) ⟨4,true,8,9⟩ .empty)))
def t343_368 : Tree := .node t343_355 ⟨4,true,6,5⟩ t356_368
def t316_368 : Tree := .node t316_342 ⟨4,true,1,18⟩ t343_368
def t369_381 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,14⟩ .empty) ⟨4,true,9,9⟩ (.node .empty ⟨4,true,10,4⟩ .empty)) ⟨4,true,10,5⟩ (.node (.node .empty ⟨4,true,10,6⟩ .empty) ⟨4,true,10,12⟩ .empty)) ⟨4,true,10,16⟩ (.node (.node (.node .empty ⟨4,true,10,18⟩ .empty) ⟨4,true,13,1⟩ .empty) ⟨4,true,13,2⟩ (.node (.node .empty ⟨4,true,13,9⟩ .empty) ⟨4,true,13,10⟩ .empty)))
def t382_394 : Tree := (.node (.node (.node (.node .empty ⟨4,true,14,1⟩ .empty) ⟨5,true,0,7⟩ (.node .empty ⟨5,true,0,13⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,11⟩ .empty) ⟨5,true,2,3⟩ .empty)) ⟨5,true,2,11⟩ (.node (.node (.node .empty ⟨5,true,2,15⟩ .empty) ⟨5,true,3,7⟩ .empty) ⟨5,true,3,13⟩ (.node (.node .empty ⟨5,true,4,11⟩ .empty) ⟨5,true,5,0⟩ .empty)))
def t369_394 : Tree := .node t369_381 ⟨4,true,13,14⟩ t382_394
def t395_407 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,4⟩ .empty) ⟨5,true,5,7⟩ (.node .empty ⟨5,true,5,11⟩ .empty)) ⟨5,true,5,12⟩ (.node (.node .empty ⟨5,true,5,13⟩ .empty) ⟨5,true,5,15⟩ .empty)) ⟨5,true,5,16⟩ (.node (.node (.node .empty ⟨5,true,7,3⟩ .empty) ⟨5,true,7,11⟩ .empty) ⟨5,true,7,15⟩ (.node (.node .empty ⟨5,true,8,3⟩ .empty) ⟨5,true,9,3⟩ .empty)))
def t408_420 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,15⟩ .empty) ⟨5,true,11,7⟩ (.node .empty ⟨5,true,11,13⟩ .empty)) ⟨5,true,12,3⟩ (.node (.node .empty ⟨5,true,12,11⟩ .empty) ⟨5,true,12,15⟩ .empty)) ⟨5,true,14,3⟩ (.node (.node (.node .empty ⟨5,true,14,11⟩ .empty) ⟨5,true,14,15⟩ .empty) ⟨5,true,15,3⟩ (.node (.node .empty ⟨5,true,15,11⟩ .empty) ⟨5,true,15,15⟩ .empty)))
def t395_420 : Tree := .node t395_407 ⟨5,true,9,11⟩ t408_420
def t369_420 : Tree := .node t369_394 ⟨5,true,5,3⟩ t395_420
def t316_420 : Tree := .node t316_368 ⟨4,true,8,10⟩ t369_420
def t211_420 : Tree := .node t211_315 ⟨3,true,14,14⟩ t316_420
def t0_420 : Tree := .node t0_210 ⟨2,true,7,5⟩ t211_420
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 10, 5, 9, 0, 6, 0, 7, 0, 8, 5, 14, 11, 4, 0, 12, 0, 10, 0, 13, 5, 15, 16, 8, 0, 13, 0, 0],#[0, 1, 3, 2, 15, 14, 4, 9, 7, 5, 13, 6, 13, 5, 8, 0, 0, 0, 11, 10, 15, 14, 12, 9, 7, 5, 8, 0, 15, 14, 16, 9, 7, 17, 0, 18, 13, 17],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2),(true,9)],[(false,4),(false,8),(false,13)],[(true,5)],[(true,6)],[(true,7),(true,14)],[(true,4)],[(true,3),(true,11)],[(false,9)],[(true,10)],[(true,12),(true,15)],[(true,8)],[(true,13)],[(false,14)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4),(true,6),(true,12)],[(true,5)],[(false,4),(false,12),(false,16)],[(false,7),(false,13)],[(true,3),(true,11),(true,15)],[(true,9)],[(false,9)],[(false,11)],[(false,5),(false,6),(false,18)],[(true,2),(true,10),(true,14)],[(false,2),(false,10),(false,14)],[(false,15)],[(true,16),(true,18)],[(true,17)]],
  t0_420⟩
theorem check0_13 : t0_13.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check14_26 : t14_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node13 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,1⟩ = true := by decide
theorem check0_26 : t0_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node13 check0_13 check14_26
theorem check27_39 : t27_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check40_52 : t40_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node39 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,6,0⟩ = true := by decide
theorem check27_52 : t27_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node39 check27_39 check40_52
theorem node26 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,13,7⟩ = true := by decide
theorem check0_52 : t0_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node26 check0_26 check27_52
theorem check53_66 : t53_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check67_79 : t67_79.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node66 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,10,12⟩ = true := by decide
theorem check53_79 : t53_79.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node66 check53_66 check67_79
theorem check80_92 : t80_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check93_105 : t93_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,14,11⟩ = true := by decide
theorem check80_105 : t80_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check80_92 check93_105
theorem node79 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,9,0⟩ = true := by decide
theorem check53_105 : t53_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node79 check53_79 check80_105
theorem node52 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,1⟩ = true := by decide
theorem check0_105 : t0_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node52 check0_52 check53_105
theorem check106_119 : t106_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check120_132 : t120_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node119 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,0,6⟩ = true := by decide
theorem check106_132 : t106_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node119 check106_119 check120_132
theorem check133_145 : t133_145.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check146_158 : t146_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node145 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,8,2⟩ = true := by decide
theorem check133_158 : t133_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node145 check133_145 check146_158
theorem node132 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,4⟩ = true := by decide
theorem check106_158 : t106_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node132 check106_132 check133_158
theorem check159_171 : t159_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check172_184 : t172_184.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node171 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,13,9⟩ = true := by decide
theorem check159_184 : t159_184.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node171 check159_171 check172_184
theorem check185_197 : t185_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check198_210 : t198_210.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node197 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,5,6⟩ = true := by decide
theorem check185_210 : t185_210.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node197 check185_197 check198_210
theorem node184 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,1,6⟩ = true := by decide
theorem check159_210 : t159_210.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node184 check159_184 check185_210
theorem node158 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,9,4⟩ = true := by decide
theorem check106_210 : t106_210.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node158 check106_158 check159_210
theorem node105 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,15,16⟩ = true := by decide
theorem check0_210 : t0_210.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node105 check0_105 check106_210
theorem check211_224 : t211_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check225_237 : t225_237.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,12,17⟩ = true := by decide
theorem check211_237 : t211_237.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node224 check211_224 check225_237
theorem check238_250 : t238_250.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check251_263 : t251_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node250 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,5,14⟩ = true := by decide
theorem check238_263 : t238_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node250 check238_250 check251_263
theorem node237 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,15⟩ = true := by decide
theorem check211_263 : t211_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node237 check211_237 check238_263
theorem check264_276 : t264_276.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check277_289 : t277_289.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node276 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,2,10⟩ = true := by decide
theorem check264_289 : t264_289.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node276 check264_276 check277_289
theorem check290_302 : t290_302.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check303_315 : t303_315.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node302 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,9,2⟩ = true := by decide
theorem check290_315 : t290_315.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node302 check290_302 check303_315
theorem node289 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,5⟩ = true := by decide
theorem check264_315 : t264_315.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node289 check264_289 check290_315
theorem node263 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,9⟩ = true := by decide
theorem check211_315 : t211_315.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node263 check211_263 check264_315
theorem check316_329 : t316_329.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check330_342 : t330_342.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node329 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,2⟩ = true := by decide
theorem check316_342 : t316_342.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node329 check316_329 check330_342
theorem check343_355 : t343_355.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check356_368 : t356_368.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node355 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,5⟩ = true := by decide
theorem check343_368 : t343_368.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node355 check343_355 check356_368
theorem node342 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,18⟩ = true := by decide
theorem check316_368 : t316_368.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node342 check316_342 check343_368
theorem check369_381 : t369_381.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check382_394 : t382_394.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node381 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,13,14⟩ = true := by decide
theorem check369_394 : t369_394.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node381 check369_381 check382_394
theorem check395_407 : t395_407.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check408_420 : t408_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node407 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,9,11⟩ = true := by decide
theorem check395_420 : t395_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node407 check395_407 check408_420
theorem node394 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,3⟩ = true := by decide
theorem check369_420 : t369_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node394 check369_394 check395_420
theorem node368 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,10⟩ = true := by decide
theorem check316_420 : t316_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node368 check316_368 check369_420
theorem node315 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,14,14⟩ = true := by decide
theorem check211_420 : t211_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node315 check211_315 check316_420
theorem node210 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,7,5⟩ = true := by decide
theorem check0_420 : t0_420.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node210 check0_210 check211_420
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_420
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M029
