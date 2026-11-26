import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M073
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,9,0⟩ .empty) ⟨0,false,9,1⟩ (.node (.node .empty ⟨0,false,9,4⟩ .empty) ⟨0,false,9,8⟩ .empty)) ⟨0,false,9,9⟩ (.node (.node (.node .empty ⟨0,false,12,0⟩ .empty) ⟨0,false,12,4⟩ .empty) ⟨0,false,12,8⟩ (.node .empty ⟨1,false,0,5⟩ .empty)))
def t11_21 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,7⟩ .empty) ⟨1,false,7,0⟩ .empty) ⟨1,false,7,1⟩ (.node (.node .empty ⟨1,false,7,4⟩ .empty) ⟨1,false,7,7⟩ .empty)) ⟨1,false,7,9⟩ (.node (.node (.node .empty ⟨1,false,7,14⟩ .empty) ⟨1,false,10,1⟩ .empty) ⟨1,false,10,9⟩ (.node .empty ⟨1,false,10,14⟩ .empty)))
def t0_21 : Tree := .node t0_10 ⟨1,false,1,0⟩ t11_21
def t22_32 : Tree := (.node (.node (.node (.node .empty ⟨1,false,13,7⟩ .empty) ⟨1,false,16,0⟩ .empty) ⟨1,false,16,7⟩ (.node (.node .empty ⟨1,false,17,0⟩ .empty) ⟨1,false,17,1⟩ .empty)) ⟨1,false,17,4⟩ (.node (.node (.node .empty ⟨1,false,17,7⟩ .empty) ⟨1,false,17,9⟩ .empty) ⟨1,false,17,14⟩ (.node .empty ⟨1,false,18,1⟩ .empty)))
def t33_42 : Tree := (.node (.node (.node (.node .empty ⟨1,false,18,9⟩ .empty) ⟨1,false,18,14⟩ .empty) ⟨1,true,6,0⟩ (.node .empty ⟨1,true,6,3⟩ .empty)) ⟨1,true,6,5⟩ (.node (.node (.node .empty ⟨1,true,6,11⟩ .empty) ⟨1,true,6,15⟩ .empty) ⟨1,true,7,3⟩ (.node .empty ⟨1,true,7,11⟩ .empty)))
def t22_42 : Tree := .node t22_32 ⟨1,false,18,7⟩ t33_42
def t0_42 : Tree := .node t0_21 ⟨1,false,13,0⟩ t22_42
def t43_53 : Tree := (.node (.node (.node (.node .empty ⟨1,true,13,3⟩ .empty) ⟨1,true,13,11⟩ .empty) ⟨1,true,13,15⟩ (.node (.node .empty ⟨1,true,16,0⟩ .empty) ⟨1,true,16,3⟩ .empty)) ⟨1,true,16,5⟩ (.node (.node (.node .empty ⟨1,true,16,11⟩ .empty) ⟨1,true,16,15⟩ .empty) ⟨1,true,17,3⟩ (.node .empty ⟨1,true,17,11⟩ .empty)))
def t54_63 : Tree := (.node (.node (.node (.node .empty ⟨1,true,18,3⟩ .empty) ⟨1,true,18,11⟩ .empty) ⟨1,true,18,15⟩ (.node .empty ⟨2,false,1,4⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,8,6⟩ .empty) ⟨2,false,8,13⟩ (.node .empty ⟨2,false,14,0⟩ .empty)))
def t43_63 : Tree := .node t43_53 ⟨1,true,17,15⟩ t54_63
def t64_74 : Tree := (.node (.node (.node (.node .empty ⟨2,false,14,13⟩ .empty) ⟨2,false,19,6⟩ .empty) ⟨2,false,19,13⟩ (.node (.node .empty ⟨2,true,8,0⟩ .empty) ⟨2,true,8,3⟩ .empty)) ⟨2,true,8,5⟩ (.node (.node (.node .empty ⟨2,true,8,11⟩ .empty) ⟨2,true,8,12⟩ .empty) ⟨2,true,11,0⟩ (.node .empty ⟨2,true,11,5⟩ .empty)))
def t75_84 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,8,1⟩ (.node .empty ⟨3,false,8,9⟩ .empty)) ⟨3,false,8,14⟩ (.node (.node (.node .empty ⟨3,false,9,0⟩ .empty) ⟨3,false,9,5⟩ .empty) ⟨3,false,9,12⟩ (.node .empty ⟨3,false,14,1⟩ .empty)))
def t64_84 : Tree := .node t64_74 ⟨2,true,11,12⟩ t75_84
def t43_84 : Tree := .node t43_63 ⟨2,false,14,6⟩ t64_84
def t0_84 : Tree := .node t0_42 ⟨1,true,7,15⟩ t43_84
def t85_95 : Tree := (.node (.node (.node (.node .empty ⟨3,false,14,14⟩ .empty) ⟨3,false,15,0⟩ .empty) ⟨3,false,15,5⟩ (.node (.node .empty ⟨3,false,15,12⟩ .empty) ⟨3,false,19,9⟩ .empty)) ⟨3,false,19,14⟩ (.node (.node (.node .empty ⟨3,false,20,5⟩ .empty) ⟨3,false,20,12⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,4,3⟩ .empty)))
def t96_106 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,10⟩ .empty) ⟨3,true,7,2⟩ .empty) ⟨3,true,7,10⟩ (.node (.node .empty ⟨3,true,13,2⟩ .empty) ⟨3,true,13,10⟩ .empty)) ⟨3,true,16,2⟩ (.node (.node (.node .empty ⟨3,true,16,10⟩ .empty) ⟨3,true,17,2⟩ .empty) ⟨3,true,17,10⟩ (.node .empty ⟨3,true,18,2⟩ .empty)))
def t85_106 : Tree := .node t85_95 ⟨3,true,4,11⟩ t96_106
def t107_117 : Tree := (.node (.node (.node (.node .empty ⟨4,false,0,6⟩ .empty) ⟨4,false,5,1⟩ .empty) ⟨4,false,5,4⟩ (.node (.node .empty ⟨4,false,5,8⟩ .empty) ⟨4,false,5,9⟩ .empty)) ⟨4,false,6,4⟩ (.node (.node (.node .empty ⟨4,false,6,8⟩ .empty) ⟨4,false,16,4⟩ .empty) ⟨4,false,16,8⟩ (.node .empty ⟨4,false,17,4⟩ .empty)))
def t118_127 : Tree := (.node (.node (.node (.node .empty ⟨4,true,0,4⟩ .empty) ⟨4,true,2,1⟩ .empty) ⟨4,true,7,6⟩ (.node .empty ⟨4,true,7,13⟩ .empty)) ⟨4,true,8,1⟩ (.node (.node (.node .empty ⟨4,true,8,9⟩ .empty) ⟨4,true,8,14⟩ .empty) ⟨4,true,9,4⟩ (.node .empty ⟨4,true,9,8⟩ .empty)))
def t107_127 : Tree := .node t107_117 ⟨4,false,17,8⟩ t118_127
def t85_127 : Tree := .node t85_106 ⟨3,true,18,10⟩ t107_127
def t128_138 : Tree := (.node (.node (.node (.node .empty ⟨4,true,10,13⟩ .empty) ⟨4,true,12,4⟩ .empty) ⟨4,true,12,8⟩ (.node (.node .empty ⟨4,true,14,1⟩ .empty) ⟨4,true,14,9⟩ .empty)) ⟨4,true,14,14⟩ (.node (.node (.node .empty ⟨4,true,17,6⟩ .empty) ⟨4,true,17,13⟩ .empty) ⟨4,true,18,6⟩ (.node .empty ⟨4,true,18,13⟩ .empty)))
def t139_148 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,14⟩ .empty) ⟨5,false,0,5⟩ .empty) ⟨5,false,6,7⟩ (.node .empty ⟨5,false,7,7⟩ .empty)) ⟨5,false,8,5⟩ (.node (.node (.node .empty ⟨5,false,8,12⟩ .empty) ⟨5,false,11,5⟩ .empty) ⟨5,false,11,12⟩ (.node .empty ⟨5,false,13,7⟩ .empty)))
def t128_148 : Tree := .node t128_138 ⟨4,true,19,9⟩ t139_148
def t149_159 : Tree := (.node (.node (.node (.node .empty ⟨5,false,17,7⟩ .empty) ⟨5,false,18,7⟩ .empty) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,6,11⟩ .empty) ⟨5,true,6,15⟩ .empty)) ⟨5,true,7,3⟩ (.node (.node (.node .empty ⟨5,true,7,11⟩ .empty) ⟨5,true,7,15⟩ .empty) ⟨5,true,13,3⟩ (.node .empty ⟨5,true,13,11⟩ .empty)))
def t160_169 : Tree := (.node (.node (.node (.node .empty ⟨5,true,16,3⟩ .empty) ⟨5,true,16,11⟩ .empty) ⟨5,true,16,15⟩ (.node .empty ⟨5,true,17,3⟩ .empty)) ⟨5,true,17,11⟩ (.node (.node (.node .empty ⟨5,true,17,15⟩ .empty) ⟨5,true,18,3⟩ .empty) ⟨5,true,18,11⟩ (.node .empty ⟨5,true,18,15⟩ .empty)))
def t149_169 : Tree := .node t149_159 ⟨5,true,13,15⟩ t160_169
def t128_169 : Tree := .node t128_148 ⟨5,false,16,7⟩ t149_169
def t85_169 : Tree := .node t85_127 ⟨4,true,10,6⟩ t128_169
def t0_169 : Tree := .node t0_84 ⟨3,false,14,9⟩ t85_169
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 6, 0, 7, 19, 10, 8, 9, 0, 0, 16, 0, 11, 12, 0, 0, 13, 10, 14, 15, 0, 0, 0, 17, 14, 18, 8, 10, 8, 20, 0, 0, 0],#[0, 1, 3, 2, 0, 0, 0, 4, 5, 0, 6, 9, 7, 0, 8, 0, 12, 0, 11, 10, 0, 0, 0, 4, 13, 14, 7, 0, 15, 10, 0, 8],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(false,5)],[(false,6)],[(true,7),(true,17),(true,18)],[(false,8)],[(false,7),(false,13),(false,18)],[(true,10)],[(false,11)],[(true,12)],[(true,13),(true,16)],[(false,14)],[(true,9)],[(false,16)],[(false,17)],[(true,6)],[(false,19)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3),(true,11)],[(false,4)],[(false,5)],[(false,6),(false,13)],[(false,7),(true,15)],[(true,5)],[(true,9),(true,14)],[(false,9)],[(false,8)],[(false,12)],[(true,12)],[(false,14)]],
  t0_169⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_21 : t11_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_21 : t0_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_21
theorem check22_32 : t22_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check33_42 : t33_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,18,7⟩ = true := by decide
theorem check22_42 : t22_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check22_32 check33_42
theorem node21 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,13,0⟩ = true := by decide
theorem check0_42 : t0_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node21 check0_21 check22_42
theorem check43_53 : t43_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check54_63 : t54_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,17,15⟩ = true := by decide
theorem check43_63 : t43_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check43_53 check54_63
theorem check64_74 : t64_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check75_84 : t75_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node74 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,11,12⟩ = true := by decide
theorem check64_84 : t64_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node74 check64_74 check75_84
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,14,6⟩ = true := by decide
theorem check43_84 : t43_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check43_63 check64_84
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,7,15⟩ = true := by decide
theorem check0_84 : t0_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check0_42 check43_84
theorem check85_95 : t85_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check96_106 : t96_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node95 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,4,11⟩ = true := by decide
theorem check85_106 : t85_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node95 check85_95 check96_106
theorem check107_117 : t107_117.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check118_127 : t118_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node117 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,17,8⟩ = true := by decide
theorem check107_127 : t107_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node117 check107_117 check118_127
theorem node106 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,18,10⟩ = true := by decide
theorem check85_127 : t85_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node106 check85_106 check107_127
theorem check128_138 : t128_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check139_148 : t139_148.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node138 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,9⟩ = true := by decide
theorem check128_148 : t128_148.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node138 check128_138 check139_148
theorem check149_159 : t149_159.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check160_169 : t160_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node159 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,13,15⟩ = true := by decide
theorem check149_169 : t149_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node159 check149_159 check160_169
theorem node148 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,16,7⟩ = true := by decide
theorem check128_169 : t128_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node148 check128_148 check149_169
theorem node127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,10,6⟩ = true := by decide
theorem check85_169 : t85_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node127 check85_127 check128_169
theorem node84 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,14,9⟩ = true := by decide
theorem check0_169 : t0_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node84 check0_84 check85_169
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_169
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M073
