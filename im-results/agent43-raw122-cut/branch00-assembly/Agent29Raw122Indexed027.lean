import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M027
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_13 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ (.node .empty ⟨0,false,0,7⟩ .empty)) ⟨0,false,1,4⟩ (.node (.node .empty ⟨0,false,1,7⟩ .empty) ⟨0,false,2,7⟩ .empty)) ⟨0,false,3,5⟩ (.node (.node (.node .empty ⟨0,false,3,9⟩ .empty) ⟨0,false,4,5⟩ (.node .empty ⟨0,false,4,9⟩ .empty)) ⟨0,false,5,1⟩ (.node (.node .empty ⟨0,false,5,7⟩ .empty) ⟨0,false,6,5⟩ .empty)))
def t14_27 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,4⟩ .empty) ⟨0,false,8,0⟩ (.node .empty ⟨0,false,8,7⟩ .empty)) ⟨0,false,9,5⟩ (.node (.node .empty ⟨0,false,9,9⟩ .empty) ⟨0,false,12,4⟩ .empty)) ⟨0,false,12,7⟩ (.node (.node (.node .empty ⟨0,false,13,5⟩ .empty) ⟨0,false,13,7⟩ (.node .empty ⟨0,false,13,9⟩ .empty)) ⟨0,false,14,5⟩ (.node (.node .empty ⟨0,false,14,9⟩ .empty) ⟨0,false,15,1⟩ .empty)))
def t0_27 : Tree := .node t0_13 ⟨0,false,6,9⟩ t14_27
def t28_41 : Tree := (.node (.node (.node (.node .empty ⟨0,false,15,7⟩ .empty) ⟨0,false,16,4⟩ (.node .empty ⟨0,false,17,5⟩ .empty)) ⟨0,false,17,9⟩ (.node (.node .empty ⟨0,false,18,0⟩ .empty) ⟨0,false,18,5⟩ .empty)) ⟨0,false,18,7⟩ (.node (.node (.node .empty ⟨0,false,18,9⟩ .empty) ⟨0,false,19,5⟩ (.node .empty ⟨0,false,19,9⟩ .empty)) ⟨0,false,20,4⟩ (.node (.node .empty ⟨0,false,22,5⟩ .empty) ⟨0,false,22,9⟩ .empty)))
def t42_55 : Tree := (.node (.node (.node (.node .empty ⟨0,false,23,4⟩ .empty) ⟨0,false,26,0⟩ (.node .empty ⟨0,false,26,5⟩ .empty)) ⟨0,false,26,9⟩ (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,6⟩ .empty)) ⟨0,true,1,5⟩ (.node (.node (.node .empty ⟨0,true,1,7⟩ .empty) ⟨0,true,2,4⟩ (.node .empty ⟨0,true,2,6⟩ .empty)) ⟨0,true,3,6⟩ (.node (.node .empty ⟨0,true,4,6⟩ .empty) ⟨0,true,5,5⟩ .empty)))
def t28_55 : Tree := .node t28_41 ⟨0,false,23,1⟩ t42_55
def t0_55 : Tree := .node t0_27 ⟨0,false,15,4⟩ t28_55
def t56_69 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,0⟩ .empty) ⟨0,true,6,6⟩ (.node .empty ⟨0,true,7,5⟩ .empty)) ⟨0,true,7,7⟩ (.node (.node .empty ⟨0,true,8,4⟩ .empty) ⟨0,true,8,6⟩ .empty)) ⟨0,true,9,6⟩ (.node (.node (.node .empty ⟨0,true,10,4⟩ .empty) ⟨0,true,12,5⟩ (.node .empty ⟨0,true,12,7⟩ .empty)) ⟨0,true,13,4⟩ (.node (.node .empty ⟨0,true,13,6⟩ .empty) ⟨0,true,14,4⟩ .empty)))
def t70_83 : Tree := (.node (.node (.node (.node .empty ⟨0,true,15,5⟩ .empty) ⟨0,true,15,7⟩ (.node .empty ⟨0,true,16,5⟩ .empty)) ⟨0,true,16,7⟩ (.node (.node .empty ⟨0,true,17,0⟩ .empty) ⟨0,true,17,6⟩ .empty)) ⟨0,true,18,4⟩ (.node (.node (.node .empty ⟨0,true,18,6⟩ .empty) ⟨0,true,19,4⟩ (.node .empty ⟨0,true,19,6⟩ .empty)) ⟨0,true,20,5⟩ (.node (.node .empty ⟨0,true,20,7⟩ .empty) ⟨0,true,22,4⟩ .empty)))
def t56_83 : Tree := .node t56_69 ⟨0,true,14,6⟩ t70_83
def t84_97 : Tree := (.node (.node (.node (.node .empty ⟨0,true,23,5⟩ .empty) ⟨0,true,23,7⟩ (.node .empty ⟨0,true,24,0⟩ .empty)) ⟨0,true,26,4⟩ (.node (.node .empty ⟨0,true,26,6⟩ .empty) ⟨0,true,27,4⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,2,3⟩ .empty) ⟨1,false,5,0⟩ (.node .empty ⟨1,false,7,8⟩ .empty)) ⟨1,false,12,8⟩ (.node (.node .empty ⟨1,false,13,3⟩ .empty) ⟨1,false,15,0⟩ .empty)))
def t98_111 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,8⟩ .empty) ⟨1,false,18,3⟩ (.node .empty ⟨1,false,20,8⟩ .empty)) ⟨1,false,22,3⟩ (.node (.node .empty ⟨1,false,23,0⟩ .empty) ⟨1,false,23,8⟩ .empty)) ⟨1,false,26,3⟩ (.node (.node (.node .empty ⟨1,true,1,4⟩ .empty) ⟨1,true,1,6⟩ (.node .empty ⟨1,true,2,6⟩ .empty)) ⟨1,true,5,6⟩ (.node (.node .empty ⟨1,true,7,4⟩ .empty) ⟨1,true,8,0⟩ .empty)))
def t84_111 : Tree := .node t84_97 ⟨1,false,15,8⟩ t98_111
def t56_111 : Tree := .node t56_83 ⟨0,true,22,6⟩ t84_111
def t0_111 : Tree := .node t0_55 ⟨0,true,5,7⟩ t56_111
def t112_125 : Tree := (.node (.node (.node (.node .empty ⟨1,true,12,4⟩ .empty) ⟨1,true,13,6⟩ (.node .empty ⟨1,true,15,4⟩ .empty)) ⟨1,true,15,6⟩ (.node (.node .empty ⟨1,true,16,4⟩ .empty) ⟨1,true,18,0⟩ .empty)) ⟨1,true,18,6⟩ (.node (.node (.node .empty ⟨1,true,20,4⟩ .empty) ⟨1,true,23,4⟩ (.node .empty ⟨1,true,26,0⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,3,5⟩ .empty) ⟨2,false,3,7⟩ .empty)))
def t126_139 : Tree := (.node (.node (.node (.node .empty ⟨2,false,4,7⟩ .empty) ⟨2,false,5,1⟩ (.node .empty ⟨2,false,6,5⟩ .empty)) ⟨2,false,6,7⟩ (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,9,5⟩ .empty)) ⟨2,false,9,7⟩ (.node (.node (.node .empty ⟨2,false,13,5⟩ .empty) ⟨2,false,13,7⟩ (.node .empty ⟨2,false,14,5⟩ .empty)) ⟨2,false,14,7⟩ (.node (.node .empty ⟨2,false,15,1⟩ .empty) ⟨2,false,17,5⟩ .empty)))
def t112_139 : Tree := .node t112_125 ⟨2,false,4,5⟩ t126_139
def t140_153 : Tree := (.node (.node (.node (.node .empty ⟨2,false,18,0⟩ .empty) ⟨2,false,18,5⟩ (.node .empty ⟨2,false,18,7⟩ .empty)) ⟨2,false,19,5⟩ (.node (.node .empty ⟨2,false,19,7⟩ .empty) ⟨2,false,22,5⟩ .empty)) ⟨2,false,22,7⟩ (.node (.node (.node .empty ⟨2,false,23,1⟩ .empty) ⟨2,false,26,0⟩ (.node .empty ⟨2,false,26,5⟩ .empty)) ⟨2,false,26,7⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t154_167 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,0⟩ .empty) ⟨3,false,18,1⟩ (.node .empty ⟨3,false,19,0⟩ .empty)) ⟨3,false,26,1⟩ (.node (.node .empty ⟨3,false,27,0⟩ .empty) ⟨3,true,1,2⟩ .empty)) ⟨3,true,5,2⟩ (.node (.node (.node .empty ⟨3,true,6,0⟩ .empty) ⟨3,true,10,4⟩ (.node .empty ⟨3,true,10,6⟩ .empty)) ⟨3,true,14,4⟩ (.node (.node .empty ⟨3,true,14,6⟩ .empty) ⟨3,true,15,2⟩ .empty)))
def t140_167 : Tree := .node t140_153 ⟨3,false,8,1⟩ t154_167
def t112_167 : Tree := .node t112_139 ⟨2,false,17,7⟩ t140_167
def t168_181 : Tree := (.node (.node (.node (.node .empty ⟨3,true,19,4⟩ .empty) ⟨3,true,19,6⟩ (.node .empty ⟨3,true,23,2⟩ .empty)) ⟨3,true,24,0⟩ (.node (.node .empty ⟨3,true,27,4⟩ .empty) ⟨3,true,27,6⟩ .empty)) ⟨4,false,4,3⟩ (.node (.node (.node .empty ⟨4,false,7,0⟩ .empty) ⟨4,false,9,0⟩ (.node .empty ⟨4,false,11,3⟩ .empty)) ⟨4,false,16,3⟩ (.node (.node .empty ⟨4,false,17,3⟩ .empty) ⟨4,false,19,0⟩ .empty)))
def t182_195 : Tree := (.node (.node (.node (.node .empty ⟨4,false,24,3⟩ .empty) ⟨4,false,25,0⟩ (.node .empty ⟨4,false,27,0⟩ .empty)) ⟨4,true,2,1⟩ (.node (.node .empty ⟨4,true,3,5⟩ .empty) ⟨4,true,3,7⟩ .empty)) ⟨4,true,4,5⟩ (.node (.node (.node .empty ⟨4,true,4,7⟩ .empty) ⟨4,true,6,5⟩ (.node .empty ⟨4,true,6,7⟩ .empty)) ⟨4,true,8,1⟩ (.node (.node .empty ⟨4,true,9,5⟩ .empty) ⟨4,true,9,7⟩ .empty)))
def t168_195 : Tree := .node t168_181 ⟨4,false,21,3⟩ t182_195
def t196_209 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,7⟩ .empty) ⟨4,true,14,5⟩ (.node .empty ⟨4,true,14,7⟩ .empty)) ⟨4,true,16,5⟩ (.node (.node .empty ⟨4,true,16,7⟩ .empty) ⟨4,true,17,5⟩ .empty)) ⟨4,true,17,7⟩ (.node (.node (.node .empty ⟨4,true,18,1⟩ .empty) ⟨4,true,19,5⟩ (.node .empty ⟨4,true,19,7⟩ .empty)) ⟨4,true,26,1⟩ (.node (.node .empty ⟨5,false,1,8⟩ .empty) ⟨5,false,2,8⟩ .empty)))
def t210_223 : Tree := (.node (.node (.node (.node .empty ⟨5,false,8,8⟩ .empty) ⟨5,false,12,8⟩ (.node .empty ⟨5,false,13,8⟩ .empty)) ⟨5,false,15,8⟩ (.node (.node .empty ⟨5,false,18,8⟩ .empty) ⟨5,true,1,3⟩ .empty)) ⟨5,true,5,3⟩ (.node (.node (.node .empty ⟨5,true,10,8⟩ .empty) ⟨5,true,14,8⟩ (.node .empty ⟨5,true,15,3⟩ .empty)) ⟨5,true,19,8⟩ (.node (.node .empty ⟨5,true,23,3⟩ .empty) ⟨5,true,27,8⟩ .empty)))
def t196_223 : Tree := .node t196_209 ⟨5,false,5,8⟩ t210_223
def t168_223 : Tree := .node t168_195 ⟨4,true,11,5⟩ t196_223
def t112_223 : Tree := .node t112_167 ⟨3,true,17,0⟩ t168_223
def t0_223 : Tree := .node t0_111 ⟨1,true,8,6⟩ t112_223
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 10, 20, 10, 12, 6, 8, 10, 7, 21, 22, 9, 5, 10, 20, 0, 11, 0, 0, 4, 13, 14, 15, 10, 16, 17, 18, 21, 22, 10, 7, 19, 15, 10, 16, 21, 22, 0, 0, 10, 23, 24, 26, 0, 25, 0, 0, 27, 23, 0, 11],#[0, 1, 3, 2, 0, 0, 4, 0, 0, 5, 8, 6, 0, 7, 8, 6, 9, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1),(false,12)],[(true,2),(true,8)],[(false,5)],[(true,6),(true,17)],[(true,5)],[(false,8)],[(false,3),(false,4),(false,6),(false,9),(false,14),(false,17),(false,19),(false,22)],[(true,10),(true,27)],[(true,4)],[(true,12)],[(false,13)],[(true,13),(true,18)],[(true,14),(true,19)],[(false,15)],[(true,15)],[(false,18)],[(true,3),(true,9)],[(false,7),(false,16),(false,20)],[(true,7),(true,16),(true,20)],[(true,22),(true,26)],[(false,23)],[(true,24)],[(true,23)],[(false,26)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(true,5),(true,7)],[(true,6)],[(false,5),(false,7)],[(false,8)]],
  t0_223⟩
theorem check0_13 : t0_13.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check14_27 : t14_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node13 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,6,9⟩ = true := by decide
theorem check0_27 : t0_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node13 check0_13 check14_27
theorem check28_41 : t28_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check42_55 : t42_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node41 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,23,1⟩ = true := by decide
theorem check28_55 : t28_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node41 check28_41 check42_55
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,15,4⟩ = true := by decide
theorem check0_55 : t0_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check0_27 check28_55
theorem check56_69 : t56_69.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check70_83 : t70_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node69 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,14,6⟩ = true := by decide
theorem check56_83 : t56_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node69 check56_69 check70_83
theorem check84_97 : t84_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check98_111 : t98_111.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,15,8⟩ = true := by decide
theorem check84_111 : t84_111.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check84_97 check98_111
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,22,6⟩ = true := by decide
theorem check56_111 : t56_111.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check56_83 check84_111
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,5,7⟩ = true := by decide
theorem check0_111 : t0_111.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check0_55 check56_111
theorem check112_125 : t112_125.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check126_139 : t126_139.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node125 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,5⟩ = true := by decide
theorem check112_139 : t112_139.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node125 check112_125 check126_139
theorem check140_153 : t140_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check154_167 : t154_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check140_167 : t140_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check140_153 check154_167
theorem node139 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,17,7⟩ = true := by decide
theorem check112_167 : t112_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node139 check112_139 check140_167
theorem check168_181 : t168_181.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check182_195 : t182_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node181 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,21,3⟩ = true := by decide
theorem check168_195 : t168_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node181 check168_181 check182_195
theorem check196_209 : t196_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check210_223 : t210_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node209 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,5,8⟩ = true := by decide
theorem check196_223 : t196_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node209 check196_209 check210_223
theorem node195 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,11,5⟩ = true := by decide
theorem check168_223 : t168_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node195 check168_195 check196_223
theorem node167 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,17,0⟩ = true := by decide
theorem check112_223 : t112_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node167 check112_167 check168_223
theorem node111 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,8,6⟩ = true := by decide
theorem check0_223 : t0_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node111 check0_111 check112_223
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_223
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M027
