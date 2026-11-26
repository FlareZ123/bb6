import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M072
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,4,1⟩ (.node .empty ⟨0,false,4,8⟩ .empty)) ⟨0,false,6,0⟩ (.node (.node (.node .empty ⟨0,false,6,4⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,9⟩ (.node .empty ⟨1,false,7,0⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,5⟩ .empty) ⟨1,true,1,3⟩ .empty) ⟨1,true,5,0⟩ (.node .empty ⟨1,true,5,5⟩ .empty)) ⟨1,true,7,3⟩ (.node (.node (.node .empty ⟨2,false,0,7⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,2,6⟩ (.node .empty ⟨2,true,0,8⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨1,false,7,9⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,8⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,3,5⟩ (.node .empty ⟨3,true,0,6⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,7,2⟩ .empty) ⟨4,false,0,6⟩ .empty) ⟨4,false,1,5⟩ (.node .empty ⟨4,true,0,4⟩ .empty)))
def t30_39 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,8⟩ .empty) ⟨4,true,4,6⟩ .empty) ⟨4,true,6,4⟩ (.node .empty ⟨5,false,0,5⟩ .empty)) ⟨5,false,1,9⟩ (.node (.node (.node .empty ⟨5,false,5,5⟩ .empty) ⟨5,false,7,9⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,7,3⟩ .empty)))
def t20_39 : Tree := .node t20_29 ⟨4,true,2,1⟩ t30_39
def t0_39 : Tree := .node t0_19 ⟨3,false,2,1⟩ t20_39
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 6, 0, 0, 7, 4, 2],#[0, 1, 3, 2, 0, 0, 0, 4, 5, 0, 6, 8, 9, 7, 0, 0, 3, 2, 4, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,7)],[(false,2)],[(false,1),(false,7)],[(true,4)],[(false,5)],[(true,6)]],
  #[[(false,0)],[(true,0)],[(true,1),(true,8)],[(false,1),(false,8)],[(false,9),(true,3)],[(false,4)],[(false,5)],[(true,6)],[(true,5)],[(false,6)]],
  t0_39⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,7,9⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_39 : t30_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,1⟩ = true := by decide
theorem check20_39 : t20_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_39
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check0_39 : t0_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_39
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_39
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M072
