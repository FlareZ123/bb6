import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M054
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_15 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,3⟩ (.node .empty ⟨0,false,1,16⟩ .empty)) ⟨0,false,5,3⟩ (.node (.node .empty ⟨0,false,5,16⟩ .empty) ⟨0,false,9,0⟩ (.node .empty ⟨0,false,9,4⟩ .empty))) ⟨0,false,9,12⟩ (.node (.node (.node .empty ⟨0,false,11,3⟩ .empty) ⟨0,false,11,16⟩ (.node .empty ⟨1,false,0,4⟩ .empty)) ⟨1,false,0,7⟩ (.node (.node .empty ⟨1,false,0,11⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,2,1⟩ .empty))))
def t16_30 : Tree := (.node (.node (.node (.node .empty ⟨1,false,4,0⟩ .empty) ⟨1,false,4,3⟩ (.node .empty ⟨1,false,4,11⟩ .empty)) ⟨1,false,6,0⟩ (.node (.node .empty ⟨1,false,6,3⟩ .empty) ⟨1,false,6,11⟩ (.node .empty ⟨1,false,7,1⟩ .empty))) ⟨1,false,7,15⟩ (.node (.node (.node .empty ⟨1,false,10,0⟩ .empty) ⟨1,false,10,3⟩ (.node .empty ⟨1,false,10,11⟩ .empty)) ⟨1,true,4,1⟩ (.node (.node .empty ⟨1,true,4,15⟩ .empty) ⟨1,true,6,1⟩ .empty)))
def t0_30 : Tree := .node t0_15 ⟨1,false,2,15⟩ t16_30
def t31_46 : Tree := (.node (.node (.node (.node .empty ⟨1,true,12,1⟩ .empty) ⟨1,true,12,15⟩ (.node .empty ⟨2,false,1,2⟩ .empty)) ⟨2,false,1,3⟩ (.node (.node .empty ⟨2,false,1,10⟩ .empty) ⟨2,false,1,13⟩ (.node .empty ⟨2,false,2,0⟩ .empty))) ⟨2,false,5,0⟩ (.node (.node (.node .empty ⟨2,false,5,1⟩ .empty) ⟨2,false,5,10⟩ (.node .empty ⟨2,false,5,13⟩ .empty)) ⟨2,false,11,0⟩ (.node (.node .empty ⟨2,false,11,1⟩ .empty) ⟨2,false,11,10⟩ (.node .empty ⟨2,false,11,13⟩ .empty))))
def t47_61 : Tree := (.node (.node (.node (.node .empty ⟨2,true,8,5⟩ .empty) ⟨2,true,8,17⟩ (.node .empty ⟨3,false,1,2⟩ .empty)) ⟨3,false,1,13⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,4,1⟩ .empty))) ⟨3,false,4,9⟩ (.node (.node (.node .empty ⟨3,false,5,1⟩ .empty) ⟨3,false,5,13⟩ (.node .empty ⟨3,false,6,0⟩ .empty)) ⟨3,false,6,9⟩ (.node (.node .empty ⟨3,false,11,1⟩ .empty) ⟨3,false,11,13⟩ .empty)))
def t31_61 : Tree := .node t31_46 ⟨2,true,8,0⟩ t47_61
def t0_61 : Tree := .node t0_30 ⟨1,true,6,15⟩ t31_61
def t62_77 : Tree := (.node (.node (.node (.node .empty ⟨3,false,12,9⟩ .empty) ⟨3,true,0,6⟩ (.node .empty ⟨3,true,0,14⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,4,1⟩ .empty) ⟨3,true,4,2⟩ (.node .empty ⟨3,true,4,9⟩ .empty))) ⟨3,true,4,14⟩ (.node (.node (.node .empty ⟨3,true,6,0⟩ .empty) ⟨3,true,6,2⟩ (.node .empty ⟨3,true,6,9⟩ .empty)) ⟨3,true,6,14⟩ (.node (.node .empty ⟨3,true,10,2⟩ .empty) ⟨3,true,10,14⟩ (.node .empty ⟨3,true,12,0⟩ .empty))))
def t78_92 : Tree := (.node (.node (.node (.node .empty ⟨4,false,5,0⟩ .empty) ⟨4,false,5,5⟩ (.node .empty ⟨4,false,5,17⟩ .empty)) ⟨4,false,13,0⟩ (.node (.node .empty ⟨4,false,13,5⟩ .empty) ⟨4,false,13,17⟩ (.node .empty ⟨4,true,1,2⟩ .empty))) ⟨4,true,1,13⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,0⟩ (.node .empty ⟨4,true,5,1⟩ .empty)) ⟨4,true,5,13⟩ (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,11,13⟩ .empty)))
def t62_92 : Tree := .node t62_77 ⟨3,true,12,9⟩ t78_92
def t93_107 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,8⟩ .empty) ⟨5,false,0,12⟩ (.node .empty ⟨5,false,1,0⟩ .empty)) ⟨5,false,1,4⟩ (.node (.node .empty ⟨5,false,1,12⟩ .empty) ⟨5,false,5,0⟩ (.node .empty ⟨5,false,5,4⟩ .empty))) ⟨5,false,5,12⟩ (.node (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,7⟩ (.node .empty ⟨5,true,0,11⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,10⟩ .empty) ⟨5,true,2,9⟩ .empty)))
def t108_122 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,3⟩ .empty) ⟨5,true,4,11⟩ (.node .empty ⟨5,true,5,10⟩ .empty)) ⟨5,true,6,0⟩ (.node (.node .empty ⟨5,true,6,3⟩ .empty) ⟨5,true,6,11⟩ (.node .empty ⟨5,true,7,9⟩ .empty))) ⟨5,true,8,5⟩ (.node (.node (.node .empty ⟨5,true,8,17⟩ .empty) ⟨5,true,9,4⟩ (.node .empty ⟨5,true,9,12⟩ .empty)) ⟨5,true,10,3⟩ (.node (.node .empty ⟨5,true,10,11⟩ .empty) ⟨5,true,11,10⟩ .empty)))
def t93_122 : Tree := .node t93_107 ⟨5,true,4,0⟩ t108_122
def t62_122 : Tree := .node t62_92 ⟨5,false,0,5⟩ t93_122
def t0_122 : Tree := .node t0_61 ⟨3,false,12,0⟩ t62_122
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 8, 0, 0, 0, 5, 6, 7, 0, 5, 0, 8, 0, 9, 0, 10, 0, 11, 12, 7, 0, 13, 0, 0],#[0, 1, 3, 2, 7, 6, 4, 0, 5, 0, 9, 15, 0, 0, 8, 0, 0, 0, 10, 13, 11, 0, 12, 0, 17, 0, 11, 14, 0, 0, 16, 0, 0, 0, 9, 15],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4),(true,6)],[(false,5)],[(true,5),(true,11)],[(true,2),(true,7)],[(true,8)],[(true,9)],[(true,10)],[(false,11)],[(true,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,2)],[(false,2)],[(false,7)],[(false,5),(false,17)],[(false,9)],[(false,10),(false,13)],[(false,11)],[(true,9)],[(true,13)],[(true,5),(true,17)],[(false,15)],[(false,12)]],
  t0_122⟩
theorem check0_15 : t0_15.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check16_30 : t16_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node15 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,2,15⟩ = true := by decide
theorem check0_30 : t0_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node15 check0_15 check16_30
theorem check31_46 : t31_46.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check47_61 : t47_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node46 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,8,0⟩ = true := by decide
theorem check31_61 : t31_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node46 check31_46 check47_61
theorem node30 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,6,15⟩ = true := by decide
theorem check0_61 : t0_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node30 check0_30 check31_61
theorem check62_77 : t62_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check78_92 : t78_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,12,9⟩ = true := by decide
theorem check62_92 : t62_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check62_77 check78_92
theorem check93_107 : t93_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check108_122 : t108_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,0⟩ = true := by decide
theorem check93_122 : t93_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check93_107 check108_122
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check62_122 : t62_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check62_92 check93_122
theorem node61 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,0⟩ = true := by decide
theorem check0_122 : t0_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node61 check0_61 check62_122
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_122
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M054
