import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M082
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_15 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ (.node .empty ⟨0,false,5,0⟩ .empty)) ⟨0,false,5,1⟩ (.node (.node .empty ⟨0,false,5,4⟩ .empty) ⟨0,false,5,5⟩ (.node .empty ⟨0,false,5,7⟩ .empty))) ⟨0,false,5,8⟩ (.node (.node (.node .empty ⟨0,false,5,16⟩ .empty) ⟨0,false,7,0⟩ (.node .empty ⟨0,false,7,1⟩ .empty)) ⟨0,false,7,4⟩ (.node (.node .empty ⟨0,false,7,5⟩ .empty) ⟨0,false,7,7⟩ (.node .empty ⟨0,false,7,11⟩ .empty))))
def t16_30 : Tree := (.node (.node (.node (.node .empty ⟨0,true,2,5⟩ .empty) ⟨0,true,2,7⟩ (.node .empty ⟨0,true,2,16⟩ .empty)) ⟨0,true,5,5⟩ (.node (.node .empty ⟨0,true,5,7⟩ .empty) ⟨0,true,5,13⟩ (.node .empty ⟨0,true,7,1⟩ .empty))) ⟨0,true,7,4⟩ (.node (.node (.node .empty ⟨0,true,7,5⟩ .empty) ⟨0,true,7,7⟩ (.node .empty ⟨0,true,7,11⟩ .empty)) ⟨0,true,7,16⟩ (.node (.node .empty ⟨0,true,9,5⟩ .empty) ⟨0,true,9,7⟩ .empty)))
def t0_30 : Tree := .node t0_15 ⟨0,false,7,16⟩ t16_30
def t31_46 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,2⟩ (.node .empty ⟨1,false,1,12⟩ .empty)) ⟨1,false,6,0⟩ (.node (.node .empty ⟨1,false,6,2⟩ .empty) ⟨1,false,6,6⟩ (.node .empty ⟨1,false,6,12⟩ .empty))) ⟨1,false,6,15⟩ (.node (.node (.node .empty ⟨1,false,8,0⟩ .empty) ⟨1,false,8,2⟩ (.node .empty ⟨1,false,8,6⟩ .empty)) ⟨1,false,8,12⟩ (.node (.node .empty ⟨1,false,8,15⟩ .empty) ⟨1,true,4,0⟩ (.node .empty ⟨1,true,4,3⟩ .empty))))
def t47_61 : Tree := (.node (.node (.node (.node .empty ⟨1,true,4,10⟩ .empty) ⟨1,true,6,0⟩ (.node .empty ⟨1,true,6,2⟩ .empty)) ⟨1,true,6,3⟩ (.node (.node .empty ⟨1,true,6,6⟩ .empty) ⟨1,true,6,12⟩ (.node .empty ⟨1,true,6,14⟩ .empty))) ⟨1,true,8,0⟩ (.node (.node (.node .empty ⟨1,true,8,3⟩ .empty) ⟨1,true,8,6⟩ (.node .empty ⟨1,true,8,10⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,9,0⟩ .empty) ⟨2,false,9,5⟩ .empty)))
def t31_61 : Tree := .node t31_46 ⟨1,true,4,6⟩ t47_61
def t0_61 : Tree := .node t0_30 ⟨0,true,9,16⟩ t31_61
def t62_77 : Tree := (.node (.node (.node (.node .empty ⟨2,false,9,13⟩ .empty) ⟨2,true,2,1⟩ (.node .empty ⟨2,true,2,4⟩ .empty)) ⟨2,true,2,11⟩ (.node (.node .empty ⟨2,true,9,1⟩ .empty) ⟨2,true,9,4⟩ (.node .empty ⟨2,true,9,11⟩ .empty))) ⟨3,false,2,1⟩ (.node (.node (.node .empty ⟨3,false,2,4⟩ .empty) ⟨3,false,2,8⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,3,2⟩ (.node (.node .empty ⟨3,false,3,3⟩ .empty) ⟨3,false,3,6⟩ (.node .empty ⟨3,false,3,12⟩ .empty))))
def t78_92 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,1⟩ .empty) ⟨3,false,9,4⟩ (.node .empty ⟨3,false,9,8⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,9⟩ .empty) ⟨3,true,6,2⟩ (.node .empty ⟨3,true,6,9⟩ .empty))) ⟨3,true,8,2⟩ (.node (.node (.node .empty ⟨3,true,8,9⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,4⟩ .empty)) ⟨4,true,2,8⟩ (.node (.node .empty ⟨4,true,9,1⟩ .empty) ⟨4,true,9,4⟩ .empty)))
def t62_92 : Tree := .node t62_77 ⟨3,false,3,14⟩ t78_92
def t93_108 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,2⟩ .empty) ⟨5,false,0,12⟩ (.node .empty ⟨5,false,4,2⟩ .empty)) ⟨5,false,4,6⟩ (.node (.node .empty ⟨5,false,4,12⟩ .empty) ⟨5,false,4,15⟩ (.node .empty ⟨5,false,6,2⟩ .empty))) ⟨5,false,6,3⟩ (.node (.node (.node .empty ⟨5,false,6,6⟩ .empty) ⟨5,false,6,12⟩ (.node .empty ⟨5,false,6,14⟩ .empty)) ⟨5,false,8,2⟩ (.node (.node .empty ⟨5,false,8,6⟩ .empty) ⟨5,false,8,12⟩ (.node .empty ⟨5,false,8,15⟩ .empty))))
def t109_123 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,11⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,1,6⟩ .empty)) ⟨5,true,1,10⟩ (.node (.node .empty ⟨5,true,5,4⟩ .empty) ⟨5,true,5,11⟩ (.node .empty ⟨5,true,6,3⟩ .empty))) ⟨5,true,6,6⟩ (.node (.node (.node .empty ⟨5,true,6,10⟩ .empty) ⟨5,true,7,4⟩ (.node .empty ⟨5,true,7,11⟩ .empty)) ⟨5,true,8,3⟩ (.node (.node .empty ⟨5,true,8,6⟩ .empty) ⟨5,true,8,10⟩ .empty)))
def t93_123 : Tree := .node t93_108 ⟨5,true,0,4⟩ t109_123
def t62_123 : Tree := .node t62_92 ⟨4,true,9,8⟩ t93_123
def t0_123 : Tree := .node t0_61 ⟨2,false,9,7⟩ t62_123
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 5, 0, 0, 6, 7, 9, 0, 8, 5, 9, 3, 4],#[0, 1, 3, 2, 5, 8, 13, 4, 3, 2, 6, 0, 7, 4, 6, 0, 10, 9, 0, 0, 0, 11, 14, 12, 5, 8, 15, 0, 13, 8, 16, 0, 3, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2),(false,9)],[(true,2),(true,9)],[(false,4),(false,8)],[(true,5)],[(false,6)],[(true,7)],[(true,6),(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1),(true,4)],[(false,1),(false,4),(false,16)],[(true,3),(true,6)],[(false,2),(false,12)],[(false,5),(false,7)],[(false,6)],[(true,2),(true,12),(true,14)],[(true,8)],[(false,8)],[(true,10)],[(true,11)],[(false,3),(false,14)],[(false,11)],[(false,13)],[(false,15)]],
  t0_123⟩
theorem check0_15 : t0_15.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check16_30 : t16_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node15 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,16⟩ = true := by decide
theorem check0_30 : t0_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node15 check0_15 check16_30
theorem check31_46 : t31_46.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check47_61 : t47_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node46 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,4,6⟩ = true := by decide
theorem check31_61 : t31_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node46 check31_46 check47_61
theorem node30 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,9,16⟩ = true := by decide
theorem check0_61 : t0_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node30 check0_30 check31_61
theorem check62_77 : t62_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check78_92 : t78_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,14⟩ = true := by decide
theorem check62_92 : t62_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check62_77 check78_92
theorem check93_108 : t93_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check109_123 : t109_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,4⟩ = true := by decide
theorem check93_123 : t93_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node108 check93_108 check109_123
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,8⟩ = true := by decide
theorem check62_123 : t62_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check62_92 check93_123
theorem node61 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,9,7⟩ = true := by decide
theorem check0_123 : t0_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node61 check0_61 check62_123
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_123
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M082
