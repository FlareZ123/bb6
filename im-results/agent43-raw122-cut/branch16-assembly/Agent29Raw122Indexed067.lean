import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M067
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,0,10⟩ (.node (.node .empty ⟨0,false,5,7⟩ .empty) ⟨0,false,6,0⟩ .empty)) ⟨0,false,6,4⟩ (.node (.node (.node .empty ⟨0,false,6,9⟩ .empty) ⟨0,false,8,0⟩ .empty) ⟨0,false,11,0⟩ (.node .empty ⟨0,false,11,1⟩ .empty)))
def t11_21 : Tree := (.node (.node (.node (.node .empty ⟨0,false,11,7⟩ .empty) ⟨0,false,11,9⟩ .empty) ⟨0,false,14,0⟩ (.node (.node .empty ⟨0,false,15,1⟩ .empty) ⟨0,false,15,7⟩ .empty)) ⟨0,false,16,0⟩ (.node (.node (.node .empty ⟨0,false,16,4⟩ .empty) ⟨0,false,16,9⟩ .empty) ⟨0,true,1,10⟩ (.node .empty ⟨0,true,1,12⟩ .empty)))
def t0_21 : Tree := .node t0_10 ⟨0,false,11,4⟩ t11_21
def t22_32 : Tree := (.node (.node (.node (.node .empty ⟨0,true,2,9⟩ .empty) ⟨0,true,3,2⟩ .empty) ⟨0,true,3,9⟩ (.node (.node .empty ⟨0,true,3,12⟩ .empty) ⟨0,true,4,1⟩ .empty)) ⟨0,true,4,7⟩ (.node (.node (.node .empty ⟨0,true,4,8⟩ .empty) ⟨0,true,5,0⟩ .empty) ⟨0,true,5,5⟩ (.node .empty ⟨0,true,6,1⟩ .empty)))
def t33_43 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,11⟩ .empty) ⟨0,true,7,0⟩ .empty) ⟨0,true,7,2⟩ (.node (.node .empty ⟨0,true,7,4⟩ .empty) ⟨0,true,7,9⟩ .empty)) ⟨0,true,7,12⟩ (.node (.node (.node .empty ⟨0,true,8,1⟩ .empty) ⟨0,true,8,3⟩ .empty) ⟨0,true,8,7⟩ (.node .empty ⟨0,true,8,8⟩ .empty)))
def t22_43 : Tree := .node t22_32 ⟨0,true,6,10⟩ t33_43
def t0_43 : Tree := .node t0_21 ⟨0,true,2,7⟩ t22_43
def t44_54 : Tree := (.node (.node (.node (.node .empty ⟨0,true,10,8⟩ .empty) ⟨0,true,12,1⟩ .empty) ⟨0,true,12,2⟩ (.node (.node .empty ⟨0,true,12,10⟩ .empty) ⟨0,true,12,11⟩ .empty)) ⟨0,true,12,12⟩ (.node (.node (.node .empty ⟨0,true,13,0⟩ .empty) ⟨0,true,13,1⟩ .empty) ⟨0,true,13,4⟩ (.node .empty ⟨0,true,13,7⟩ .empty)))
def t55_65 : Tree := (.node (.node (.node (.node .empty ⟨0,true,14,0⟩ .empty) ⟨0,true,14,3⟩ .empty) ⟨0,true,14,5⟩ (.node (.node .empty ⟨0,true,14,8⟩ .empty) ⟨0,true,15,0⟩ .empty)) ⟨0,true,15,5⟩ (.node (.node (.node .empty ⟨0,true,16,1⟩ .empty) ⟨0,true,16,10⟩ .empty) ⟨0,true,16,11⟩ (.node .empty ⟨1,false,1,0⟩ .empty)))
def t44_65 : Tree := .node t44_54 ⟨0,true,13,9⟩ t55_65
def t66_76 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,15⟩ .empty) ⟨1,false,7,0⟩ .empty) ⟨1,false,11,0⟩ (.node (.node .empty ⟨1,false,12,0⟩ .empty) ⟨1,false,15,0⟩ .empty)) ⟨1,true,1,9⟩ (.node (.node (.node .empty ⟨1,true,6,5⟩ .empty) ⟨1,true,7,3⟩ .empty) ⟨1,true,7,8⟩ (.node .empty ⟨1,true,12,0⟩ .empty)))
def t77_87 : Tree := (.node (.node (.node (.node .empty ⟨1,true,12,5⟩ .empty) ⟨1,true,12,8⟩ .empty) ⟨1,true,16,0⟩ (.node (.node .empty ⟨1,true,16,5⟩ .empty) ⟨2,false,2,0⟩ .empty)) ⟨2,false,2,4⟩ (.node (.node (.node .empty ⟨2,false,2,9⟩ .empty) ⟨2,false,2,14⟩ .empty) ⟨2,false,8,0⟩ (.node .empty ⟨2,false,12,0⟩ .empty)))
def t66_87 : Tree := .node t66_76 ⟨1,true,12,3⟩ t77_87
def t44_87 : Tree := .node t44_65 ⟨1,false,1,5⟩ t66_87
def t0_87 : Tree := .node t0_43 ⟨0,true,10,5⟩ t44_87
def t88_98 : Tree := (.node (.node (.node (.node .empty ⟨2,false,16,0⟩ .empty) ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ (.node (.node .empty ⟨3,false,8,1⟩ .empty) ⟨3,false,9,0⟩ .empty)) ⟨3,false,12,1⟩ (.node (.node (.node .empty ⟨3,false,13,1⟩ .empty) ⟨3,false,16,1⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,3,3⟩ .empty)))
def t99_109 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,13⟩ .empty) ⟨3,true,7,2⟩ .empty) ⟨3,true,11,2⟩ (.node (.node .empty ⟨3,true,12,2⟩ .empty) ⟨3,true,15,2⟩ .empty)) ⟨4,false,0,9⟩ (.node (.node (.node .empty ⟨4,false,2,7⟩ .empty) ⟨4,false,2,9⟩ .empty) ⟨4,false,4,1⟩ (.node .empty ⟨4,false,4,7⟩ .empty)))
def t88_109 : Tree := .node t88_98 ⟨3,true,3,8⟩ t99_109
def t110_120 : Tree := (.node (.node (.node (.node .empty ⟨4,false,7,0⟩ .empty) ⟨4,false,7,4⟩ .empty) ⟨4,false,7,9⟩ (.node (.node .empty ⟨4,false,8,1⟩ .empty) ⟨4,false,8,7⟩ .empty)) ⟨4,false,13,0⟩ (.node (.node (.node .empty ⟨4,false,13,1⟩ .empty) ⟨4,false,13,4⟩ .empty) ⟨4,false,13,7⟩ (.node .empty ⟨4,false,13,9⟩ .empty)))
def t121_131 : Tree := (.node (.node (.node (.node .empty ⟨4,true,0,9⟩ .empty) ⟨4,true,0,14⟩ .empty) ⟨4,true,1,7⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,7⟩ .empty)) ⟨4,true,2,8⟩ (.node (.node (.node .empty ⟨4,true,4,7⟩ .empty) ⟨4,true,4,9⟩ .empty) ⟨4,true,6,4⟩ (.node .empty ⟨4,true,6,7⟩ .empty)))
def t110_131 : Tree := .node t110_120 ⟨4,true,0,4⟩ t121_131
def t88_131 : Tree := .node t88_109 ⟨4,false,4,8⟩ t110_131
def t132_142 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,8,4⟩ .empty) ⟨4,true,8,7⟩ (.node (.node .empty ⟨4,true,8,9⟩ .empty) ⟨4,true,10,4⟩ .empty)) ⟨4,true,10,9⟩ (.node (.node (.node .empty ⟨4,true,11,4⟩ .empty) ⟨4,true,11,9⟩ .empty) ⟨4,true,12,1⟩ (.node .empty ⟨4,true,12,7⟩ .empty)))
def t143_153 : Tree := (.node (.node (.node (.node .empty ⟨4,true,13,7⟩ .empty) ⟨4,true,14,4⟩ .empty) ⟨4,true,14,9⟩ (.node (.node .empty ⟨4,true,16,1⟩ .empty) ⟨4,true,16,4⟩ .empty)) ⟨4,true,16,7⟩ (.node (.node (.node .empty ⟨4,true,16,9⟩ .empty) ⟨5,false,0,5⟩ .empty) ⟨5,false,0,15⟩ (.node .empty ⟨5,true,0,8⟩ .empty)))
def t132_153 : Tree := .node t132_142 ⟨4,true,13,1⟩ t143_153
def t154_164 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,8⟩ .empty) ⟨5,true,1,13⟩ .empty) ⟨5,true,2,5⟩ (.node (.node .empty ⟨5,true,3,5⟩ .empty) ⟨5,true,3,8⟩ .empty)) ⟨5,true,5,5⟩ (.node (.node (.node .empty ⟨5,true,5,8⟩ .empty) ⟨5,true,7,3⟩ .empty) ⟨5,true,7,5⟩ (.node .empty ⟨5,true,7,8⟩ .empty)))
def t165_174 : Tree := (.node (.node (.node (.node .empty ⟨5,true,11,3⟩ .empty) ⟨5,true,11,8⟩ .empty) ⟨5,true,12,3⟩ (.node .empty ⟨5,true,12,8⟩ .empty)) ⟨5,true,13,5⟩ (.node (.node (.node .empty ⟨5,true,14,5⟩ .empty) ⟨5,true,15,3⟩ .empty) ⟨5,true,15,5⟩ (.node .empty ⟨5,true,15,8⟩ .empty)))
def t154_174 : Tree := .node t154_164 ⟨5,true,10,5⟩ t165_174
def t132_174 : Tree := .node t132_153 ⟨5,true,1,3⟩ t154_174
def t88_174 : Tree := .node t88_131 ⟨4,true,6,9⟩ t132_174
def t0_174 : Tree := .node t0_87 ⟨2,false,13,0⟩ t88_174
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 10, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8, 9, 15, 0, 0, 0, 11, 0, 12, 9, 13, 9, 14, 0, 11, 0, 16, 9, 7],#[0, 1, 3, 2, 0, 0, 0, 4, 5, 11, 6, 7, 0, 0, 8, 12, 13, 9, 5, 10, 0, 0, 0, 0, 0, 0, 0, 14, 15, 0, 6, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,3)],[(true,4)],[(true,5)],[(true,6),(true,16)],[(true,7)],[(false,8),(false,12),(false,13),(false,16)],[(true,2)],[(true,10),(true,14)],[(true,11)],[(true,12)],[(true,13)],[(true,8)],[(true,15)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(false,4),(false,9)],[(false,5),(false,15)],[(true,5)],[(false,7)],[(true,8)],[(true,9)],[(true,4)],[(true,7)],[(false,8)],[(true,13)],[(false,14)]],
  t0_174⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_21 : t11_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,11,4⟩ = true := by decide
theorem check0_21 : t0_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_21
theorem check22_32 : t22_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check33_43 : t33_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,6,10⟩ = true := by decide
theorem check22_43 : t22_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check22_32 check33_43
theorem node21 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,2,7⟩ = true := by decide
theorem check0_43 : t0_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node21 check0_21 check22_43
theorem check44_54 : t44_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check55_65 : t55_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node54 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,13,9⟩ = true := by decide
theorem check44_65 : t44_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node54 check44_54 check55_65
theorem check66_76 : t66_76.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check77_87 : t77_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node76 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,12,3⟩ = true := by decide
theorem check66_87 : t66_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node76 check66_76 check77_87
theorem node65 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,5⟩ = true := by decide
theorem check44_87 : t44_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node65 check44_65 check66_87
theorem node43 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,10,5⟩ = true := by decide
theorem check0_87 : t0_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node43 check0_43 check44_87
theorem check88_98 : t88_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check99_109 : t99_109.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,8⟩ = true := by decide
theorem check88_109 : t88_109.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check88_98 check99_109
theorem check110_120 : t110_120.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check121_131 : t121_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node120 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,0,4⟩ = true := by decide
theorem check110_131 : t110_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node120 check110_120 check121_131
theorem node109 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,8⟩ = true := by decide
theorem check88_131 : t88_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node109 check88_109 check110_131
theorem check132_142 : t132_142.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check143_153 : t143_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node142 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,13,1⟩ = true := by decide
theorem check132_153 : t132_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node142 check132_142 check143_153
theorem check154_164 : t154_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check165_174 : t165_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node164 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,10,5⟩ = true := by decide
theorem check154_174 : t154_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node164 check154_164 check165_174
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check132_174 : t132_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check132_153 check154_174
theorem node131 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,9⟩ = true := by decide
theorem check88_174 : t88_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node131 check88_131 check132_174
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,13,0⟩ = true := by decide
theorem check0_174 : t0_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check0_87 check88_174
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_174
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M067
