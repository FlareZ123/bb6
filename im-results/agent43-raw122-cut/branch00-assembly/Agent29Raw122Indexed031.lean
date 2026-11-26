import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M031
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,13⟩ (.node .empty ⟨0,false,5,13⟩ .empty)) ⟨0,false,8,0⟩ (.node (.node .empty ⟨0,false,8,16⟩ .empty) ⟨0,true,0,4⟩ .empty)) ⟨0,true,0,15⟩ (.node (.node (.node .empty ⟨0,true,4,15⟩ .empty) ⟨0,true,6,15⟩ .empty) ⟨0,true,8,4⟩ (.node (.node .empty ⟨0,true,8,20⟩ .empty) ⟨1,false,0,6⟩ .empty)))
def t13_24 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,2,12⟩ .empty) ⟨1,false,4,8⟩ (.node (.node .empty ⟨1,false,4,10⟩ .empty) ⟨1,false,6,4⟩ .empty)) ⟨1,false,6,8⟩ (.node (.node (.node .empty ⟨1,false,6,10⟩ .empty) ⟨1,false,6,15⟩ .empty) ⟨1,false,7,12⟩ (.node (.node .empty ⟨1,false,11,0⟩ .empty) ⟨1,false,11,7⟩ .empty)))
def t0_24 : Tree := .node t0_12 ⟨1,false,0,10⟩ t13_24
def t25_37 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,8⟩ .empty) ⟨1,true,0,10⟩ (.node .empty ⟨1,true,4,4⟩ .empty)) ⟨1,true,4,8⟩ (.node (.node .empty ⟨1,true,4,10⟩ .empty) ⟨1,true,4,15⟩ .empty)) ⟨1,true,6,8⟩ (.node (.node (.node .empty ⟨1,true,6,10⟩ .empty) ⟨1,true,6,15⟩ .empty) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,5,3⟩ .empty) ⟨2,false,5,14⟩ .empty)))
def t38_49 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,6⟩ .empty) ⟨2,false,8,22⟩ .empty) ⟨2,false,12,0⟩ (.node (.node .empty ⟨2,false,12,4⟩ .empty) ⟨2,false,12,15⟩ .empty)) ⟨2,false,12,20⟩ (.node (.node (.node .empty ⟨2,true,1,5⟩ .empty) ⟨2,true,1,9⟩ .empty) ⟨2,true,5,7⟩ (.node (.node .empty ⟨2,true,5,9⟩ .empty) ⟨3,false,2,1⟩ .empty)))
def t25_49 : Tree := .node t25_37 ⟨2,false,8,2⟩ t38_49
def t0_49 : Tree := .node t0_24 ⟨1,false,11,23⟩ t25_49
def t50_62 : Tree := (.node (.node (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,5,6⟩ (.node .empty ⟨3,false,5,22⟩ .empty)) ⟨3,false,6,1⟩ (.node (.node .empty ⟨3,false,6,5⟩ .empty) ⟨3,false,6,21⟩ .empty)) ⟨3,false,12,1⟩ (.node (.node (.node .empty ⟨3,false,12,17⟩ .empty) ⟨3,false,13,0⟩ .empty) ⟨3,false,13,3⟩ (.node (.node .empty ⟨3,false,13,14⟩ .empty) ⟨3,false,13,19⟩ .empty)))
def t63_74 : Tree := (.node (.node (.node (.node .empty ⟨3,true,4,11⟩ .empty) ⟨3,true,6,11⟩ .empty) ⟨3,true,9,1⟩ (.node (.node .empty ⟨3,true,9,5⟩ .empty) ⟨3,true,9,21⟩ .empty)) ⟨3,true,11,2⟩ (.node (.node (.node .empty ⟨3,true,11,18⟩ .empty) ⟨4,false,0,5⟩ .empty) ⟨4,false,0,9⟩ (.node (.node .empty ⟨4,false,1,7⟩ .empty) ⟨4,false,1,9⟩ .empty)))
def t50_74 : Tree := .node t50_62 ⟨3,true,1,2⟩ t63_74
def t75_87 : Tree := (.node (.node (.node (.node .empty ⟨4,false,5,9⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,5⟩ .empty)) ⟨4,true,2,21⟩ (.node (.node .empty ⟨4,true,5,2⟩ .empty) ⟨4,true,5,6⟩ .empty)) ⟨4,true,5,22⟩ (.node (.node (.node .empty ⟨4,true,7,5⟩ .empty) ⟨4,true,7,21⟩ .empty) ⟨4,true,10,0⟩ (.node (.node .empty ⟨4,true,10,4⟩ .empty) ⟨4,true,10,20⟩ .empty)))
def t88_99 : Tree := (.node (.node (.node (.node .empty ⟨4,true,12,17⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,1,14⟩ (.node (.node .empty ⟨5,true,4,12⟩ .empty) ⟨5,true,5,14⟩ .empty)) ⟨5,true,6,12⟩ (.node (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,7⟩ .empty) ⟨5,true,9,23⟩ (.node (.node .empty ⟨5,true,11,3⟩ .empty) ⟨5,true,11,19⟩ .empty)))
def t75_99 : Tree := .node t75_87 ⟨4,true,12,1⟩ t88_99
def t50_99 : Tree := .node t50_74 ⟨4,false,5,7⟩ t75_99
def t0_99 : Tree := .node t0_49 ⟨3,false,3,0⟩ t50_99
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 8, 0, 0, 0, 5, 6, 7, 0, 5, 0, 8, 9, 11, 0, 10, 0, 0, 0, 12, 13, 0, 0, 0],#[0, 1, 3, 2, 12, 11, 4, 17, 7, 5, 14, 6, 12, 11, 16, 8, 9, 0, 0, 10, 9, 0, 0, 0, 13, 0, 0, 0, 15, 17, 7, 9, 0, 0, 19, 18, 0, 0, 20, 17, 23, 21, 14, 22, 12, 11, 16, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4),(true,6)],[(false,5)],[(true,5)],[(true,2),(true,7)],[(false,8)],[(true,9)],[(true,8)],[(true,11)],[(false,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(true,5)],[(false,4),(false,15)],[(true,7)],[(false,8),(false,10),(true,15)],[(true,9)],[(true,2),(true,6),(true,22)],[(false,2),(false,6),(false,22)],[(false,12)],[(false,5),(false,21)],[(false,14)],[(false,7),(false,23)],[(true,3),(true,14),(true,19)],[(true,17)],[(false,17)],[(false,19)],[(true,20)],[(true,21)],[(false,20)]],
  t0_99⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_24 : t13_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,0,10⟩ = true := by decide
theorem check0_24 : t0_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_24
theorem check25_37 : t25_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check38_49 : t38_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node37 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,8,2⟩ = true := by decide
theorem check25_49 : t25_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node37 check25_37 check38_49
theorem node24 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,11,23⟩ = true := by decide
theorem check0_49 : t0_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node24 check0_24 check25_49
theorem check50_62 : t50_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check63_74 : t63_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node62 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check50_74 : t50_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node62 check50_62 check63_74
theorem check75_87 : t75_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check88_99 : t88_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,12,1⟩ = true := by decide
theorem check75_99 : t75_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check75_87 check88_99
theorem node74 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,5,7⟩ = true := by decide
theorem check50_99 : t50_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node74 check50_74 check75_99
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check0_99 : t0_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check0_49 check50_99
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_99
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M031
