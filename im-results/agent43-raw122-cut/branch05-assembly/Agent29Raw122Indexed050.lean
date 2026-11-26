import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M050
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
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,2,3⟩ (.node .empty ⟨0,false,2,11⟩ .empty)) ⟨0,false,7,0⟩ (.node (.node (.node .empty ⟨0,false,7,4⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,3⟩ (.node .empty ⟨1,false,1,8⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨1,false,5,10⟩ .empty) ⟨1,true,3,1⟩ .empty) ⟨1,true,3,10⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,2,1⟩ (.node (.node (.node .empty ⟨2,false,2,7⟩ .empty) ⟨2,false,2,9⟩ .empty) ⟨2,true,6,0⟩ (.node .empty ⟨2,true,6,5⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨1,false,5,1⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,9⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,3,6⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,3,0⟩ (.node (.node (.node .empty ⟨3,true,3,6⟩ .empty) ⟨4,false,4,0⟩ .empty) ⟨4,false,4,5⟩ (.node .empty ⟨4,true,2,1⟩ .empty)))
def t30_38 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,true,0,4⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,1,8⟩ .empty)) ⟨5,true,2,7⟩ (.node (.node .empty ⟨5,true,5,6⟩ .empty) ⟨5,true,6,5⟩ (.node .empty ⟨5,true,7,4⟩ .empty)))
def t20_38 : Tree := .node t20_29 ⟨4,true,2,9⟩ t30_38
def t0_38 : Tree := .node t0_19 ⟨3,false,2,1⟩ t20_38
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 5, 0, 4, 0, 0, 0, 6, 0, 7, 0, 1],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 0, 6, 10, 7, 9, 8, 0, 4, 0, 8, 2, 11, 0, 0, 0],
  #[[(false,0)],[(true,0),(true,7)],[(true,1)],[(false,2)],[(true,3)],[(true,2)],[(true,5)],[(true,6)]],
  #[[(false,0)],[(true,0)],[(true,1),(true,9)],[(false,1)],[(false,3),(false,8)],[(false,4)],[(false,5)],[(false,6)],[(false,7),(false,9)],[(true,6)],[(true,5)],[(false,10)]],
  t0_38⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,1⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_38 : t30_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,9⟩ = true := by decide
theorem check20_38 : t20_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_38
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check0_38 : t0_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_38
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_38
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M050
