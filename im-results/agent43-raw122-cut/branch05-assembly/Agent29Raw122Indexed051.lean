import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M051
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_11 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,0,10⟩ (.node (.node .empty ⟨0,false,2,2⟩ .empty) ⟨0,false,2,14⟩ .empty)) ⟨0,false,5,1⟩ (.node (.node (.node .empty ⟨0,false,5,6⟩ .empty) ⟨0,false,5,15⟩ .empty) ⟨0,false,7,2⟩ (.node (.node .empty ⟨0,false,7,14⟩ .empty) ⟨1,false,1,0⟩ .empty)))
def t12_22 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,1,11⟩ .empty) ⟨1,true,5,1⟩ (.node (.node .empty ⟨1,true,5,6⟩ .empty) ⟨1,true,5,15⟩ .empty)) ⟨1,true,7,0⟩ (.node (.node (.node .empty ⟨1,true,7,2⟩ .empty) ⟨1,true,7,8⟩ .empty) ⟨1,true,7,10⟩ (.node .empty ⟨1,true,7,14⟩ .empty)))
def t0_22 : Tree := .node t0_11 ⟨1,false,1,3⟩ t12_22
def t23_33 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,1⟩ .empty) ⟨2,false,2,8⟩ .empty) ⟨2,false,2,10⟩ (.node (.node .empty ⟨2,false,2,12⟩ .empty) ⟨2,false,8,0⟩ .empty)) ⟨2,false,8,7⟩ (.node (.node (.node .empty ⟨2,false,8,9⟩ .empty) ⟨2,false,8,11⟩ .empty) ⟨2,true,3,1⟩ (.node .empty ⟨2,true,3,6⟩ .empty)))
def t34_44 : Tree := (.node (.node (.node (.node .empty ⟨2,true,6,0⟩ .empty) ⟨2,true,6,2⟩ .empty) ⟨2,true,6,8⟩ (.node (.node .empty ⟨2,true,6,10⟩ .empty) ⟨2,true,6,14⟩ .empty)) ⟨2,true,8,1⟩ (.node (.node (.node .empty ⟨2,true,8,6⟩ .empty) ⟨2,true,8,15⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,2,12⟩ .empty)))
def t23_44 : Tree := .node t23_33 ⟨2,true,3,15⟩ t34_44
def t0_44 : Tree := .node t0_22 ⟨2,false,2,0⟩ t23_44
def t45_55 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,7⟩ .empty) ⟨3,false,3,9⟩ .empty) ⟨3,false,3,11⟩ (.node (.node .empty ⟨3,false,7,2⟩ .empty) ⟨3,false,7,14⟩ .empty)) ⟨3,false,8,1⟩ (.node (.node (.node .empty ⟨3,false,8,6⟩ .empty) ⟨3,false,8,15⟩ .empty) ⟨3,false,9,0⟩ (.node .empty ⟨3,false,9,2⟩ .empty)))
def t56_66 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,10⟩ .empty) ⟨3,false,9,14⟩ .empty) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,13⟩ .empty) ⟨3,true,3,0⟩ .empty)) ⟨3,true,3,7⟩ (.node (.node (.node .empty ⟨3,true,3,9⟩ .empty) ⟨3,true,3,11⟩ .empty) ⟨3,true,5,6⟩ (.node .empty ⟨4,false,4,0⟩ .empty)))
def t45_66 : Tree := .node t45_55 ⟨3,false,9,8⟩ t56_66
def t67_77 : Tree := (.node (.node (.node (.node .empty ⟨4,false,4,8⟩ .empty) ⟨4,false,4,10⟩ .empty) ⟨4,false,4,14⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,12⟩ .empty)) ⟨4,true,7,2⟩ (.node (.node (.node .empty ⟨4,true,7,14⟩ .empty) ⟨5,false,0,5⟩ .empty) ⟨5,false,0,11⟩ (.node .empty ⟨5,true,0,4⟩ .empty)))
def t78_88 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,9⟩ .empty) ⟨5,true,1,11⟩ (.node (.node .empty ⟨5,true,2,8⟩ .empty) ⟨5,true,2,10⟩ .empty)) ⟨5,true,5,7⟩ (.node (.node (.node .empty ⟨5,true,5,9⟩ .empty) ⟨5,true,5,11⟩ .empty) ⟨5,true,7,8⟩ (.node .empty ⟨5,true,7,10⟩ .empty)))
def t67_88 : Tree := .node t67_77 ⟨5,true,0,10⟩ t78_88
def t45_88 : Tree := .node t45_66 ⟨4,false,4,2⟩ t67_88
def t0_88 : Tree := .node t0_44 ⟨3,false,3,0⟩ t45_88
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 5, 0, 4, 0, 0, 6, 7, 0, 0, 8, 5, 9, 0, 0, 0],#[0, 1, 3, 2, 7, 6, 4, 0, 5, 0, 0, 0, 0, 14, 8, 12, 9, 15, 10, 12, 11, 15, 10, 12, 3, 13, 0, 0, 7, 6, 0, 14],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,3)],[(true,2),(true,7)],[(false,5)],[(true,5)],[(false,7)],[(false,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,12)],[(false,3)],[(false,4)],[(true,2),(true,14)],[(false,2),(false,14)],[(false,7)],[(false,8)],[(false,9),(false,11)],[(false,10)],[(true,7),(true,9),(true,11)],[(true,12)],[(true,6),(true,15)],[(true,8),(true,10)]],
  t0_88⟩
theorem check0_11 : t0_11.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check12_22 : t12_22.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node11 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,3⟩ = true := by decide
theorem check0_22 : t0_22.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node11 check0_11 check12_22
theorem check23_33 : t23_33.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check34_44 : t34_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node33 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,3,15⟩ = true := by decide
theorem check23_44 : t23_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node33 check23_33 check34_44
theorem node22 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,0⟩ = true := by decide
theorem check0_44 : t0_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node22 check0_22 check23_44
theorem check45_55 : t45_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check56_66 : t56_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,9,8⟩ = true := by decide
theorem check45_66 : t45_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check45_55 check56_66
theorem check67_77 : t67_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check78_88 : t78_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,10⟩ = true := by decide
theorem check67_88 : t67_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check67_77 check78_88
theorem node66 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,2⟩ = true := by decide
theorem check45_88 : t45_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node66 check45_66 check67_88
theorem node44 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check0_88 : t0_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node44 check0_44 check45_88
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_88
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M051
