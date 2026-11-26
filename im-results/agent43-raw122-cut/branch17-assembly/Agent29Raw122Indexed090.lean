import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M090
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,2⟩ (.node .empty ⟨0,false,0,3⟩ .empty)) ⟨0,false,0,8⟩ (.node (.node .empty ⟨0,false,0,16⟩ .empty) ⟨0,false,0,17⟩ (.node .empty ⟨0,false,0,19⟩ .empty))) ⟨0,false,2,0⟩ (.node (.node (.node .empty ⟨0,false,2,9⟩ .empty) ⟨0,false,2,16⟩ (.node .empty ⟨0,false,2,22⟩ .empty)) ⟨0,false,8,0⟩ (.node (.node .empty ⟨0,false,8,9⟩ .empty) ⟨0,false,8,16⟩ .empty)))
def t15_28 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,1⟩ .empty) ⟨0,true,0,7⟩ (.node .empty ⟨0,true,0,15⟩ .empty)) ⟨0,true,1,0⟩ (.node (.node .empty ⟨0,true,1,6⟩ .empty) ⟨0,true,1,13⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,1,1⟩ .empty) ⟨1,false,1,4⟩ (.node .empty ⟨1,false,1,11⟩ .empty)) ⟨1,false,1,12⟩ (.node (.node .empty ⟨1,false,1,13⟩ .empty) ⟨1,false,7,0⟩ .empty)))
def t0_28 : Tree := .node t0_14 ⟨0,false,8,22⟩ t15_28
def t29_43 : Tree := (.node (.node (.node (.node .empty ⟨1,false,7,12⟩ .empty) ⟨1,false,7,13⟩ (.node .empty ⟨1,false,7,16⟩ .empty)) ⟨1,false,7,26⟩ (.node (.node .empty ⟨1,true,1,1⟩ .empty) ⟨1,true,1,7⟩ (.node .empty ⟨1,true,1,14⟩ .empty))) ⟨1,true,1,15⟩ (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,2⟩ (.node .empty ⟨2,false,2,5⟩ .empty)) ⟨2,false,2,17⟩ (.node (.node .empty ⟨2,false,2,18⟩ .empty) ⟨2,false,2,20⟩ .empty)))
def t44_57 : Tree := (.node (.node (.node (.node .empty ⟨2,false,4,0⟩ .empty) ⟨2,false,4,6⟩ (.node .empty ⟨2,false,4,12⟩ .empty)) ⟨2,false,4,13⟩ (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,8,2⟩ .empty)) ⟨2,false,8,3⟩ (.node (.node (.node .empty ⟨2,false,8,5⟩ .empty) ⟨2,false,8,12⟩ (.node .empty ⟨2,false,8,13⟩ .empty)) ⟨2,false,8,17⟩ (.node (.node .empty ⟨2,false,8,18⟩ .empty) ⟨2,false,8,19⟩ .empty)))
def t29_57 : Tree := .node t29_43 ⟨2,false,2,25⟩ t44_57
def t0_57 : Tree := .node t0_28 ⟨1,false,7,6⟩ t29_57
def t58_72 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,23⟩ .empty) ⟨2,false,8,25⟩ (.node .empty ⟨2,true,0,4⟩ .empty)) ⟨2,true,0,11⟩ (.node (.node .empty ⟨2,true,0,12⟩ .empty) ⟨2,true,0,13⟩ (.node .empty ⟨2,true,2,0⟩ .empty))) ⟨2,true,2,3⟩ (.node (.node (.node .empty ⟨2,true,2,5⟩ .empty) ⟨2,true,2,17⟩ (.node .empty ⟨2,true,2,18⟩ .empty)) ⟨2,true,2,25⟩ (.node (.node .empty ⟨2,true,3,0⟩ .empty) ⟨2,true,3,6⟩ .empty)))
def t73_86 : Tree := (.node (.node (.node (.node .empty ⟨2,true,3,13⟩ .empty) ⟨2,true,3,16⟩ (.node .empty ⟨2,true,3,26⟩ .empty)) ⟨2,true,9,0⟩ (.node (.node .empty ⟨2,true,9,6⟩ .empty) ⟨2,true,9,12⟩ .empty)) ⟨2,true,9,13⟩ (.node (.node (.node .empty ⟨2,true,9,16⟩ .empty) ⟨2,true,9,26⟩ (.node .empty ⟨3,false,1,2⟩ .empty)) ⟨3,false,1,5⟩ (.node (.node .empty ⟨3,false,1,18⟩ .empty) ⟨3,false,1,20⟩ .empty)))
def t58_86 : Tree := .node t58_72 ⟨2,true,3,12⟩ t73_86
def t87_100 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,1⟩ (.node .empty ⟨3,false,4,4⟩ .empty)) ⟨3,false,4,10⟩ (.node (.node .empty ⟨3,false,4,11⟩ .empty) ⟨3,false,5,0⟩ .empty)) ⟨3,false,5,2⟩ (.node (.node (.node .empty ⟨3,false,5,3⟩ .empty) ⟨3,false,5,5⟩ (.node .empty ⟨3,false,5,17⟩ .empty)) ⟨3,false,5,18⟩ (.node (.node .empty ⟨3,false,5,20⟩ .empty) ⟨3,false,5,25⟩ .empty)))
def t101_114 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,2⟩ .empty) ⟨3,false,8,5⟩ (.node .empty ⟨3,false,8,10⟩ .empty)) ⟨3,false,8,11⟩ (.node (.node .empty ⟨3,false,8,18⟩ .empty) ⟨3,false,8,20⟩ .empty)) ⟨3,false,9,0⟩ (.node (.node (.node .empty ⟨3,false,9,1⟩ .empty) ⟨3,false,9,2⟩ (.node .empty ⟨3,false,9,4⟩ .empty)) ⟨3,false,9,5⟩ (.node (.node .empty ⟨3,false,9,10⟩ .empty) ⟨3,false,9,11⟩ .empty)))
def t87_114 : Tree := .node t87_100 ⟨3,false,8,1⟩ t101_114
def t58_114 : Tree := .node t58_86 ⟨3,false,2,1⟩ t87_114
def t0_114 : Tree := .node t0_57 ⟨2,false,8,20⟩ t58_114
def t115_129 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,18⟩ .empty) ⟨3,false,9,20⟩ (.node .empty ⟨3,false,9,25⟩ .empty)) ⟨3,true,0,10⟩ (.node (.node .empty ⟨3,true,0,11⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,3,1⟩ .empty))) ⟨3,true,3,4⟩ (.node (.node (.node .empty ⟨3,true,3,10⟩ .empty) ⟨3,true,3,11⟩ (.node .empty ⟨3,true,3,14⟩ .empty)) ⟨3,true,3,15⟩ (.node (.node .empty ⟨3,true,3,24⟩ .empty) ⟨3,true,7,2⟩ .empty)))
def t130_143 : Tree := (.node (.node (.node (.node .empty ⟨3,true,7,11⟩ .empty) ⟨3,true,7,18⟩ (.node .empty ⟨3,true,7,20⟩ .empty)) ⟨3,true,9,1⟩ (.node (.node .empty ⟨3,true,9,4⟩ .empty) ⟨3,true,9,10⟩ .empty)) ⟨3,true,9,11⟩ (.node (.node (.node .empty ⟨3,true,9,14⟩ .empty) ⟨3,true,9,15⟩ (.node .empty ⟨3,true,9,24⟩ .empty)) ⟨4,true,1,2⟩ (.node (.node .empty ⟨4,true,1,5⟩ .empty) ⟨4,true,1,17⟩ .empty)))
def t115_143 : Tree := .node t115_129 ⟨3,true,7,10⟩ t130_143
def t144_158 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,20⟩ .empty) ⟨4,true,1,25⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,4,0⟩ (.node (.node .empty ⟨4,true,4,6⟩ .empty) ⟨4,true,4,12⟩ (.node .empty ⟨4,true,4,13⟩ .empty))) ⟨4,true,6,0⟩ (.node (.node (.node .empty ⟨4,true,6,2⟩ .empty) ⟨4,true,6,3⟩ (.node .empty ⟨4,true,6,5⟩ .empty)) ⟨4,true,6,12⟩ (.node (.node .empty ⟨4,true,6,13⟩ .empty) ⟨4,true,6,17⟩ .empty)))
def t159_172 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,19⟩ .empty) ⟨4,true,6,20⟩ (.node .empty ⟨4,true,6,23⟩ .empty)) ⟨4,true,6,25⟩ (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,8,2⟩ .empty)) ⟨4,true,8,5⟩ (.node (.node (.node .empty ⟨4,true,8,10⟩ .empty) ⟨4,true,8,11⟩ (.node .empty ⟨4,true,8,17⟩ .empty)) ⟨4,true,8,18⟩ (.node (.node .empty ⟨4,true,8,20⟩ .empty) ⟨4,true,8,25⟩ .empty)))
def t144_172 : Tree := .node t144_158 ⟨4,true,6,18⟩ t159_172
def t115_172 : Tree := .node t115_143 ⟨4,true,1,18⟩ t144_172
def t173_187 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,14⟩ .empty) ⟨5,false,0,15⟩ (.node .empty ⟨5,false,0,18⟩ .empty)) ⟨5,false,1,0⟩ (.node (.node .empty ⟨5,false,1,9⟩ .empty) ⟨5,false,1,16⟩ (.node .empty ⟨5,false,2,1⟩ .empty))) ⟨5,false,2,7⟩ (.node (.node (.node .empty ⟨5,false,2,14⟩ .empty) ⟨5,false,2,15⟩ (.node .empty ⟨5,false,2,21⟩ .empty)) ⟨5,false,8,1⟩ (.node (.node .empty ⟨5,false,8,7⟩ .empty) ⟨5,false,8,14⟩ .empty)))
def t188_201 : Tree := (.node (.node (.node (.node .empty ⟨5,false,8,21⟩ .empty) ⟨5,true,0,4⟩ (.node .empty ⟨5,true,0,11⟩ .empty)) ⟨5,true,0,12⟩ (.node (.node .empty ⟨5,true,0,13⟩ .empty) ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,5⟩ (.node (.node (.node .empty ⟨5,true,1,17⟩ .empty) ⟨5,true,1,18⟩ (.node .empty ⟨5,true,1,25⟩ .empty)) ⟨5,true,2,4⟩ (.node (.node .empty ⟨5,true,2,11⟩ .empty) ⟨5,true,2,14⟩ .empty)))
def t173_201 : Tree := .node t173_187 ⟨5,false,8,15⟩ t188_201
def t202_215 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,24⟩ .empty) ⟨5,true,3,0⟩ (.node .empty ⟨5,true,3,6⟩ .empty)) ⟨5,true,3,12⟩ (.node (.node .empty ⟨5,true,3,13⟩ .empty) ⟨5,true,3,16⟩ .empty)) ⟨5,true,3,26⟩ (.node (.node (.node .empty ⟨5,true,7,3⟩ .empty) ⟨5,true,7,5⟩ (.node .empty ⟨5,true,7,12⟩ .empty)) ⟨5,true,7,13⟩ (.node (.node .empty ⟨5,true,7,17⟩ .empty) ⟨5,true,7,18⟩ .empty)))
def t216_229 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,23⟩ .empty) ⟨5,true,7,25⟩ (.node .empty ⟨5,true,8,4⟩ .empty)) ⟨5,true,8,11⟩ (.node (.node .empty ⟨5,true,8,14⟩ .empty) ⟨5,true,8,15⟩ .empty)) ⟨5,true,8,24⟩ (.node (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,6⟩ (.node .empty ⟨5,true,9,12⟩ .empty)) ⟨5,true,9,13⟩ (.node (.node .empty ⟨5,true,9,16⟩ .empty) ⟨5,true,9,26⟩ .empty)))
def t202_229 : Tree := .node t202_215 ⟨5,true,7,19⟩ t216_229
def t173_229 : Tree := .node t173_201 ⟨5,true,2,15⟩ t202_229
def t115_229 : Tree := .node t115_172 ⟨5,false,0,5⟩ t173_229
def t0_229 : Tree := .node t0_114 ⟨3,false,9,17⟩ t115_229
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 7, 0, 6, 5, 0, 0, 0, 0, 0, 0, 8, 9, 7, 0, 6],#[0, 1, 3, 2, 12, 10, 6, 4, 3, 5, 13, 11, 9, 7, 0, 8, 0, 0, 0, 0, 23, 20, 19, 18, 16, 14, 16, 15, 0, 17, 0, 17, 22, 21, 13, 11, 13, 11, 26, 24, 12, 10, 0, 0, 0, 0, 26, 24, 0, 25, 13, 11, 22, 21],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(false,4)],[(true,3),(true,9)],[(true,2),(true,8)],[(true,7)],[(false,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,4)],[(false,3)],[(true,6)],[(true,7)],[(false,6)],[(true,2),(true,20)],[(true,5),(true,17),(true,18),(true,25)],[(false,2),(false,20)],[(false,5),(false,17),(false,18),(false,25)],[(true,12)],[(true,13)],[(false,12),(false,13)],[(true,14),(true,15)],[(true,11)],[(false,11)],[(true,10)],[(true,16),(true,26)],[(false,16),(false,26)],[(false,10)],[(true,19),(true,23)],[(true,24)],[(false,19),(false,23)]],
  t0_229⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_28 : t15_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,8,22⟩ = true := by decide
theorem check0_28 : t0_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_28
theorem check29_43 : t29_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check44_57 : t44_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node43 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,25⟩ = true := by decide
theorem check29_57 : t29_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node43 check29_43 check44_57
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,7,6⟩ = true := by decide
theorem check0_57 : t0_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check0_28 check29_57
theorem check58_72 : t58_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check73_86 : t73_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,3,12⟩ = true := by decide
theorem check58_86 : t58_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check58_72 check73_86
theorem check87_100 : t87_100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check101_114 : t101_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node100 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check87_114 : t87_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node100 check87_100 check101_114
theorem node86 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check58_114 : t58_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node86 check58_86 check87_114
theorem node57 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,8,20⟩ = true := by decide
theorem check0_114 : t0_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node57 check0_57 check58_114
theorem check115_129 : t115_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check130_143 : t130_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node129 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,7,10⟩ = true := by decide
theorem check115_143 : t115_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node129 check115_129 check130_143
theorem check144_158 : t144_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check159_172 : t159_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node158 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,18⟩ = true := by decide
theorem check144_172 : t144_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node158 check144_158 check159_172
theorem node143 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,18⟩ = true := by decide
theorem check115_172 : t115_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node143 check115_143 check144_172
theorem check173_187 : t173_187.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check188_201 : t188_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node187 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,8,15⟩ = true := by decide
theorem check173_201 : t173_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node187 check173_187 check188_201
theorem check202_215 : t202_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check216_229 : t216_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node215 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,19⟩ = true := by decide
theorem check202_229 : t202_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node215 check202_215 check216_229
theorem node201 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,15⟩ = true := by decide
theorem check173_229 : t173_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node201 check173_201 check202_229
theorem node172 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check115_229 : t115_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node172 check115_172 check173_229
theorem node114 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,9,17⟩ = true := by decide
theorem check0_229 : t0_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node114 check0_114 check115_229
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_229
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M090
