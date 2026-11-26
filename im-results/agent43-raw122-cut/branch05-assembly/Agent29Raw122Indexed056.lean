import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M056
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,2⟩ .empty) ⟨0,false,1,16⟩ (.node .empty ⟨0,false,5,2⟩ .empty)) ⟨0,false,5,16⟩ (.node (.node .empty ⟨0,false,9,0⟩ .empty) ⟨0,false,9,4⟩ (.node .empty ⟨0,false,9,12⟩ .empty))) ⟨0,false,11,2⟩ (.node (.node (.node .empty ⟨0,false,11,16⟩ .empty) ⟨0,true,1,2⟩ (.node .empty ⟨0,true,1,16⟩ .empty)) ⟨0,true,2,1⟩ (.node (.node .empty ⟨0,true,2,15⟩ .empty) ⟨0,true,5,2⟩ (.node .empty ⟨0,true,5,16⟩ .empty))))
def t17_33 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,7,15⟩ .empty) ⟨0,true,8,0⟩ .empty) ⟨0,true,8,5⟩ (.node .empty ⟨0,true,8,17⟩ .empty)) ⟨0,true,11,2⟩ (.node (.node .empty ⟨0,true,11,16⟩ .empty) ⟨1,false,0,4⟩ (.node .empty ⟨1,false,0,7⟩ .empty))) ⟨1,false,0,11⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,4,0⟩ (.node .empty ⟨1,false,4,3⟩ .empty)) ⟨1,false,4,11⟩ (.node (.node .empty ⟨1,false,6,0⟩ .empty) ⟨1,false,6,3⟩ (.node .empty ⟨1,false,6,11⟩ .empty))))
def t0_33 : Tree := .node t0_16 ⟨0,true,7,1⟩ t17_33
def t34_50 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,10,3⟩ .empty) ⟨1,false,10,11⟩ .empty) ⟨1,true,2,1⟩ (.node .empty ⟨1,true,2,15⟩ .empty)) ⟨1,true,4,1⟩ (.node (.node .empty ⟨1,true,4,15⟩ .empty) ⟨1,true,6,1⟩ (.node .empty ⟨1,true,6,15⟩ .empty))) ⟨1,true,7,1⟩ (.node (.node (.node .empty ⟨1,true,7,15⟩ .empty) ⟨1,true,12,1⟩ (.node .empty ⟨1,true,12,15⟩ .empty)) ⟨2,false,1,2⟩ (.node (.node .empty ⟨2,false,1,3⟩ .empty) ⟨2,false,1,10⟩ (.node .empty ⟨2,false,1,13⟩ .empty))))
def t51_66 : Tree := (.node (.node (.node (.node .empty ⟨2,false,5,0⟩ .empty) ⟨2,false,5,1⟩ (.node .empty ⟨2,false,5,10⟩ .empty)) ⟨2,false,5,13⟩ (.node (.node .empty ⟨2,false,11,0⟩ .empty) ⟨2,false,11,1⟩ (.node .empty ⟨2,false,11,10⟩ .empty))) ⟨2,false,11,13⟩ (.node (.node (.node .empty ⟨3,false,1,2⟩ .empty) ⟨3,false,1,13⟩ (.node .empty ⟨3,false,2,1⟩ .empty)) ⟨3,false,3,0⟩ (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,4,9⟩ (.node .empty ⟨3,false,5,1⟩ .empty))))
def t34_66 : Tree := .node t34_50 ⟨2,false,2,0⟩ t51_66
def t0_66 : Tree := .node t0_33 ⟨1,false,10,0⟩ t34_66
def t67_83 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,6,0⟩ .empty) ⟨3,false,6,9⟩ .empty) ⟨3,false,11,1⟩ (.node .empty ⟨3,false,11,13⟩ .empty)) ⟨3,false,12,0⟩ (.node (.node .empty ⟨3,false,12,9⟩ .empty) ⟨3,true,0,6⟩ (.node .empty ⟨3,true,0,14⟩ .empty))) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,4,1⟩ .empty) ⟨3,true,4,2⟩ (.node .empty ⟨3,true,4,9⟩ .empty)) ⟨3,true,4,14⟩ (.node (.node .empty ⟨3,true,6,0⟩ .empty) ⟨3,true,6,2⟩ (.node .empty ⟨3,true,6,9⟩ .empty))))
def t84_99 : Tree := (.node (.node (.node (.node .empty ⟨3,true,10,2⟩ .empty) ⟨3,true,10,14⟩ (.node .empty ⟨3,true,12,0⟩ .empty)) ⟨3,true,12,9⟩ (.node (.node .empty ⟨4,false,5,0⟩ .empty) ⟨4,false,5,5⟩ (.node .empty ⟨4,false,5,17⟩ .empty))) ⟨4,false,13,0⟩ (.node (.node (.node .empty ⟨4,false,13,5⟩ .empty) ⟨4,false,13,17⟩ (.node .empty ⟨4,true,1,2⟩ .empty)) ⟨4,true,1,13⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,0⟩ (.node .empty ⟨4,true,5,1⟩ .empty))))
def t67_99 : Tree := .node t67_83 ⟨3,true,6,14⟩ t84_99
def t100_116 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,11,13⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,false,0,8⟩ .empty)) ⟨5,false,0,12⟩ (.node (.node .empty ⟨5,false,1,0⟩ .empty) ⟨5,false,1,4⟩ (.node .empty ⟨5,false,1,12⟩ .empty))) ⟨5,false,5,0⟩ (.node (.node (.node .empty ⟨5,false,5,4⟩ .empty) ⟨5,false,5,12⟩ (.node .empty ⟨5,true,0,4⟩ .empty)) ⟨5,true,0,7⟩ (.node (.node .empty ⟨5,true,0,11⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,1,10⟩ .empty))))
def t117_132 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,0⟩ .empty) ⟨5,true,4,3⟩ (.node .empty ⟨5,true,4,11⟩ .empty)) ⟨5,true,5,10⟩ (.node (.node .empty ⟨5,true,6,0⟩ .empty) ⟨5,true,6,3⟩ (.node .empty ⟨5,true,6,11⟩ .empty))) ⟨5,true,7,9⟩ (.node (.node (.node .empty ⟨5,true,8,5⟩ .empty) ⟨5,true,8,17⟩ (.node .empty ⟨5,true,9,4⟩ .empty)) ⟨5,true,9,12⟩ (.node (.node .empty ⟨5,true,10,3⟩ .empty) ⟨5,true,10,11⟩ (.node .empty ⟨5,true,11,10⟩ .empty))))
def t100_132 : Tree := .node t100_116 ⟨5,true,2,9⟩ t117_132
def t67_132 : Tree := .node t67_99 ⟨4,true,5,13⟩ t100_132
def t0_132 : Tree := .node t0_66 ⟨3,false,5,13⟩ t67_132
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 8, 0, 0, 0, 5, 6, 7, 0, 5, 0, 8, 0, 9, 0, 10, 0, 11, 12, 7, 0, 13, 0, 0],#[0, 1, 3, 2, 7, 6, 4, 0, 5, 0, 9, 15, 0, 0, 8, 0, 0, 0, 10, 13, 11, 0, 12, 0, 17, 0, 11, 14, 0, 0, 0, 16, 0, 0, 9, 15],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4),(true,6)],[(false,5)],[(true,5),(true,11)],[(true,2),(true,7)],[(true,8)],[(true,9)],[(true,10)],[(false,11)],[(true,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,2)],[(false,2)],[(false,7)],[(false,5),(false,17)],[(false,9)],[(false,10),(false,13)],[(false,11)],[(true,9)],[(true,13)],[(true,5),(true,17)],[(true,15)],[(false,12)]],
  t0_132⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_33 : t17_33.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,1⟩ = true := by decide
theorem check0_33 : t0_33.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_33
theorem check34_50 : t34_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check51_66 : t51_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node50 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,0⟩ = true := by decide
theorem check34_66 : t34_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node50 check34_50 check51_66
theorem node33 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,0⟩ = true := by decide
theorem check0_66 : t0_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node33 check0_33 check34_66
theorem check67_83 : t67_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_99 : t84_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,14⟩ = true := by decide
theorem check67_99 : t67_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check67_83 check84_99
theorem check100_116 : t100_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check117_132 : t117_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,9⟩ = true := by decide
theorem check100_132 : t100_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check100_116 check117_132
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,13⟩ = true := by decide
theorem check67_132 : t67_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check67_99 check100_132
theorem node66 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,5,13⟩ = true := by decide
theorem check0_132 : t0_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node66 check0_66 check67_132
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_132
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M056
