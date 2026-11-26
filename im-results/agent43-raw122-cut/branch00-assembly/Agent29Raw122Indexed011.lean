import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M011
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,9⟩ .empty) ⟨0,false,2,9⟩ (.node .empty ⟨0,false,2,13⟩ .empty)) ⟨0,true,0,4⟩ (.node (.node (.node .empty ⟨0,true,1,12⟩ .empty) ⟨0,true,2,4⟩ .empty) ⟨0,true,5,0⟩ (.node .empty ⟨0,true,5,11⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨1,false,0,5⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,8⟩ (.node .empty ⟨1,false,2,1⟩ .empty)) ⟨1,false,2,16⟩ (.node (.node (.node .empty ⟨1,false,7,8⟩ .empty) ⟨1,false,7,12⟩ .empty) ⟨1,true,0,13⟩ (.node .empty ⟨1,true,0,15⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨0,true,7,12⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨1,true,2,13⟩ .empty) ⟨1,true,2,15⟩ .empty) ⟨1,true,3,0⟩ (.node .empty ⟨1,true,3,12⟩ .empty)) ⟨1,true,7,5⟩ (.node (.node (.node .empty ⟨2,false,1,4⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,2,6⟩ (.node .empty ⟨2,false,2,11⟩ .empty)))
def t30_39 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,8,11⟩ .empty) ⟨2,false,10,4⟩ (.node .empty ⟨2,true,1,13⟩ .empty)) ⟨2,true,1,15⟩ (.node (.node (.node .empty ⟨2,true,4,5⟩ .empty) ⟨2,true,7,0⟩ .empty) ⟨2,true,7,12⟩ (.node .empty ⟨2,true,10,13⟩ .empty)))
def t20_39 : Tree := .node t20_29 ⟨2,false,4,12⟩ t30_39
def t0_39 : Tree := .node t0_19 ⟨1,true,1,5⟩ t20_39
def t40_49 : Tree := (.node (.node (.node (.node .empty ⟨3,false,1,6⟩ .empty) ⟨3,false,2,1⟩ .empty) ⟨3,false,2,10⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,3,2⟩ (.node (.node (.node .empty ⟨3,false,4,3⟩ .empty) ⟨3,false,4,7⟩ .empty) ⟨3,false,4,14⟩ (.node .empty ⟨3,false,7,2⟩ .empty)))
def t50_59 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,10⟩ .empty) ⟨3,false,9,0⟩ .empty) ⟨3,false,9,2⟩ (.node .empty ⟨3,false,10,6⟩ .empty)) ⟨3,false,10,11⟩ (.node (.node (.node .empty ⟨3,true,0,7⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,2,10⟩ (.node .empty ⟨3,true,3,3⟩ .empty)))
def t40_59 : Tree := .node t40_49 ⟨3,false,8,1⟩ t50_59
def t60_69 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,14⟩ .empty) ⟨3,true,7,2⟩ .empty) ⟨4,false,5,1⟩ (.node .empty ⟨4,false,5,10⟩ .empty)) ⟨4,true,1,6⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,10⟩ .empty) ⟨4,true,5,6⟩ (.node .empty ⟨4,true,5,11⟩ .empty)))
def t70_78 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,8⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,2,11⟩ (.node .empty ⟨5,true,3,8⟩ .empty)) ⟨5,true,3,12⟩ (.node (.node .empty ⟨5,true,6,0⟩ .empty) ⟨5,true,6,2⟩ (.node .empty ⟨5,true,7,3⟩ .empty)))
def t60_78 : Tree := .node t60_69 ⟨4,true,7,2⟩ t70_78
def t40_78 : Tree := .node t40_59 ⟨3,true,3,7⟩ t60_78
def t0_78 : Tree := .node t0_39 ⟨2,true,10,15⟩ t40_78
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 7, 0, 5, 10, 0, 0, 6, 0, 0, 8, 2, 9, 0, 0, 0, 4, 0],#[0, 1, 3, 2, 11, 10, 4, 6, 5, 0, 0, 15, 8, 7, 0, 6, 9, 0, 0, 0, 3, 2, 12, 14, 13, 16, 0, 5, 0, 6, 0, 5, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,7)],[(false,2)],[(false,1),(false,10)],[(true,3)],[(true,5)],[(true,2)],[(false,7)],[(false,8)],[(false,4)]],
  #[[(false,0)],[(true,0)],[(true,1),(true,10)],[(false,1),(false,10)],[(false,3)],[(false,4),(true,13),(true,15)],[(true,3),(true,7),(true,14)],[(true,6)],[(false,6)],[(false,8)],[(true,2)],[(false,2)],[(false,11)],[(false,12)],[(true,11)],[(true,5)],[(true,12)]],
  t0_78⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,12⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_39 : t30_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,12⟩ = true := by decide
theorem check20_39 : t20_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_39
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,5⟩ = true := by decide
theorem check0_39 : t0_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_39
theorem check40_49 : t40_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check50_59 : t50_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check40_59 : t40_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check40_49 check50_59
theorem check60_69 : t60_69.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check70_78 : t70_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node69 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,2⟩ = true := by decide
theorem check60_78 : t60_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node69 check60_69 check70_78
theorem node59 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,7⟩ = true := by decide
theorem check40_78 : t40_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node59 check40_59 check60_78
theorem node39 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,10,15⟩ = true := by decide
theorem check0_78 : t0_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node39 check0_39 check40_78
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_78
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M011
