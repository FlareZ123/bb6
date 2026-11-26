import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M071
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,2,0⟩ .empty) ⟨0,false,2,1⟩ (.node .empty ⟨0,false,2,2⟩ .empty)) ⟨0,false,2,4⟩ (.node (.node (.node .empty ⟨0,false,2,6⟩ .empty) ⟨0,false,5,0⟩ .empty) ⟨0,false,5,1⟩ (.node .empty ⟨0,false,5,4⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨0,false,9,1⟩ .empty) ⟨0,false,9,4⟩ .empty) ⟨0,true,2,0⟩ (.node .empty ⟨0,true,2,3⟩ .empty)) ⟨1,false,0,5⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,2,0⟩ .empty) ⟨1,false,5,0⟩ (.node .empty ⟨1,false,8,0⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨0,false,9,0⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,8⟩ .empty) ⟨1,true,2,0⟩ .empty) ⟨1,true,2,3⟩ (.node .empty ⟨1,true,5,0⟩ .empty)) ⟨1,true,5,1⟩ (.node (.node (.node .empty ⟨1,true,5,3⟩ .empty) ⟨1,true,5,4⟩ .empty) ⟨1,true,8,0⟩ (.node .empty ⟨1,true,8,3⟩ .empty)))
def t30_38 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,5,0⟩ .empty) ⟨2,false,5,1⟩ (.node .empty ⟨2,false,5,4⟩ .empty)) ⟨2,false,9,0⟩ (.node (.node .empty ⟨3,false,1,2⟩ .empty) ⟨3,false,1,6⟩ (.node .empty ⟨3,false,2,1⟩ .empty)))
def t20_38 : Tree := .node t20_29 ⟨2,false,1,3⟩ t30_38
def t0_38 : Tree := .node t0_19 ⟨1,true,1,3⟩ t20_38
def t39_48 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,4,4⟩ .empty) ⟨3,false,5,1⟩ (.node .empty ⟨3,false,6,0⟩ .empty)) ⟨3,false,9,1⟩ (.node (.node (.node .empty ⟨3,true,0,7⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,2,2⟩ (.node .empty ⟨3,true,5,2⟩ .empty)))
def t49_58 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,3⟩ .empty) ⟨3,true,8,2⟩ .empty) ⟨4,false,0,4⟩ (.node .empty ⟨4,false,0,9⟩ .empty)) ⟨4,false,5,4⟩ (.node (.node (.node .empty ⟨4,false,7,0⟩ .empty) ⟨4,false,7,1⟩ .empty) ⟨4,false,7,4⟩ (.node .empty ⟨4,false,9,4⟩ .empty)))
def t39_58 : Tree := .node t39_48 ⟨3,true,6,0⟩ t49_58
def t59_68 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,2⟩ .empty) ⟨4,true,1,4⟩ .empty) ⟨4,true,1,6⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,4⟩ (.node (.node (.node .empty ⟨4,true,5,1⟩ .empty) ⟨4,true,5,4⟩ .empty) ⟨4,true,7,4⟩ (.node .empty ⟨4,true,9,1⟩ .empty)))
def t69_77 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,3⟩ .empty) ⟨5,true,0,3⟩ .empty) ⟨5,true,0,8⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,2,3⟩ (.node (.node .empty ⟨5,true,5,3⟩ .empty) ⟨5,true,6,3⟩ (.node .empty ⟨5,true,8,3⟩ .empty)))
def t59_77 : Tree := .node t59_68 ⟨4,true,9,4⟩ t69_77
def t39_77 : Tree := .node t39_58 ⟨4,true,0,4⟩ t59_77
def t0_77 : Tree := .node t0_38 ⟨3,false,3,0⟩ t39_77
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 0, 0, 0, 0, 6, 2, 0, 7, 0, 8, 0, 9, 6, 8],#[0, 1, 3, 2, 8, 7, 5, 4, 3, 6, 0, 0, 8, 7, 0, 0, 0, 9, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,5)],[(false,2)],[(false,1)],[(true,2)],[(false,5),(false,9)],[(true,6)],[(true,7),(true,9)],[(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(false,3)],[(true,4)],[(true,2),(true,6)],[(false,2),(false,6)],[(true,8)]],
  t0_77⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,9,0⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_38 : t30_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,1,3⟩ = true := by decide
theorem check20_38 : t20_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_38
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,3⟩ = true := by decide
theorem check0_38 : t0_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_38
theorem check39_48 : t39_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_58 : t49_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,0⟩ = true := by decide
theorem check39_58 : t39_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check39_48 check49_58
theorem check59_68 : t59_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check69_77 : t69_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node68 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,4⟩ = true := by decide
theorem check59_77 : t59_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node68 check59_68 check69_77
theorem node58 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,0,4⟩ = true := by decide
theorem check39_77 : t39_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node58 check39_58 check59_77
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check0_77 : t0_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check0_38 check39_77
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_77
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M071
