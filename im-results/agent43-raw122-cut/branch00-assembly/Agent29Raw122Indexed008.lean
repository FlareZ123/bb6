import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M008
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,9⟩ (.node .empty ⟨0,false,0,23⟩ .empty)) ⟨0,true,0,4⟩ (.node (.node .empty ⟨0,true,1,17⟩ .empty) ⟨0,true,1,23⟩ .empty)) ⟨0,true,1,31⟩ (.node (.node (.node .empty ⟨0,true,3,12⟩ .empty) ⟨0,true,3,26⟩ .empty) ⟨0,true,5,23⟩ (.node (.node .empty ⟨0,true,5,31⟩ .empty) ⟨0,true,7,26⟩ .empty)))
def t13_24 : Tree := (.node (.node (.node (.node .empty ⟨0,true,11,23⟩ .empty) ⟨0,true,11,31⟩ .empty) ⟨0,true,13,12⟩ (.node (.node .empty ⟨0,true,13,26⟩ .empty) ⟨1,false,0,5⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,1,8⟩ .empty) ⟨1,false,1,22⟩ .empty) ⟨1,false,2,13⟩ (.node (.node .empty ⟨1,false,2,27⟩ .empty) ⟨1,false,6,27⟩ .empty)))
def t0_24 : Tree := .node t0_12 ⟨0,true,11,17⟩ t13_24
def t25_37 : Tree := (.node (.node (.node (.node .empty ⟨1,false,12,27⟩ .empty) ⟨1,true,0,18⟩ (.node .empty ⟨1,true,0,32⟩ .empty)) ⟨1,true,3,32⟩ (.node (.node .empty ⟨1,true,7,18⟩ .empty) ⟨1,true,7,32⟩ .empty)) ⟨1,true,13,32⟩ (.node (.node (.node .empty ⟨2,false,1,4⟩ .empty) ⟨2,false,1,18⟩ .empty) ⟨2,false,1,32⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,6⟩ .empty)))
def t38_49 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,14⟩ .empty) ⟨2,false,6,20⟩ .empty) ⟨2,false,6,28⟩ (.node (.node .empty ⟨2,false,7,0⟩ .empty) ⟨2,false,8,0⟩ .empty)) ⟨2,false,9,12⟩ (.node (.node (.node .empty ⟨2,false,9,18⟩ .empty) ⟨2,false,9,26⟩ .empty) ⟨2,false,9,32⟩ (.node (.node .empty ⟨2,false,12,14⟩ .empty) ⟨2,false,12,20⟩ .empty)))
def t25_49 : Tree := .node t25_37 ⟨2,false,2,20⟩ t38_49
def t0_49 : Tree := .node t0_24 ⟨1,false,12,13⟩ t25_49
def t50_62 : Tree := (.node (.node (.node (.node .empty ⟨2,false,14,0⟩ .empty) ⟨2,false,15,18⟩ (.node .empty ⟨2,false,15,26⟩ .empty)) ⟨2,false,15,32⟩ (.node (.node .empty ⟨2,true,6,0⟩ .empty) ⟨2,true,6,1⟩ .empty)) ⟨2,true,6,2⟩ (.node (.node (.node .empty ⟨2,true,6,10⟩ .empty) ⟨2,true,6,24⟩ .empty) ⟨2,true,7,0⟩ (.node (.node .empty ⟨2,true,7,1⟩ .empty) ⟨2,true,7,2⟩ .empty)))
def t63_74 : Tree := (.node (.node (.node (.node .empty ⟨2,true,7,24⟩ .empty) ⟨2,true,8,0⟩ .empty) ⟨2,true,8,1⟩ (.node (.node .empty ⟨2,true,8,2⟩ .empty) ⟨2,true,8,10⟩ .empty)) ⟨2,true,8,24⟩ (.node (.node (.node .empty ⟨2,true,12,1⟩ .empty) ⟨2,true,12,2⟩ .empty) ⟨2,true,12,10⟩ (.node (.node .empty ⟨2,true,12,24⟩ .empty) ⟨2,true,13,0⟩ .empty)))
def t50_74 : Tree := .node t50_62 ⟨2,true,7,10⟩ t63_74
def t75_87 : Tree := (.node (.node (.node (.node .empty ⟨2,true,13,2⟩ .empty) ⟨2,true,13,10⟩ (.node .empty ⟨2,true,13,24⟩ .empty)) ⟨2,true,14,0⟩ (.node (.node .empty ⟨2,true,14,1⟩ .empty) ⟨2,true,14,2⟩ .empty)) ⟨2,true,14,10⟩ (.node (.node (.node .empty ⟨2,true,14,24⟩ .empty) ⟨3,false,1,6⟩ .empty) ⟨3,false,1,20⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t88_99 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,17⟩ .empty) ⟨3,false,4,23⟩ .empty) ⟨3,false,4,31⟩ (.node (.node .empty ⟨3,false,6,2⟩ .empty) ⟨3,false,6,10⟩ .empty)) ⟨3,false,6,24⟩ (.node (.node (.node .empty ⟨3,false,7,1⟩ .empty) ⟨3,false,7,2⟩ .empty) ⟨3,false,7,10⟩ (.node (.node .empty ⟨3,false,7,24⟩ .empty) ⟨3,false,8,0⟩ .empty)))
def t75_99 : Tree := .node t75_87 ⟨3,false,4,3⟩ t88_99
def t50_99 : Tree := .node t50_74 ⟨2,true,13,1⟩ t75_99
def t0_99 : Tree := .node t0_49 ⟨2,false,12,28⟩ t50_99
def t100_112 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,2⟩ .empty) ⟨3,false,8,10⟩ (.node .empty ⟨3,false,8,24⟩ .empty)) ⟨3,false,9,14⟩ (.node (.node .empty ⟨3,false,9,20⟩ .empty) ⟨3,false,9,28⟩ .empty)) ⟨3,false,10,11⟩ (.node (.node (.node .empty ⟨3,false,10,17⟩ .empty) ⟨3,false,10,23⟩ .empty) ⟨3,false,10,25⟩ (.node (.node .empty ⟨3,false,10,31⟩ .empty) ⟨3,false,12,10⟩ .empty)))
def t113_124 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,2⟩ .empty) ⟨3,false,13,10⟩ .empty) ⟨3,false,13,24⟩ (.node (.node .empty ⟨3,false,14,1⟩ .empty) ⟨3,false,14,2⟩ .empty)) ⟨3,false,14,10⟩ (.node (.node (.node .empty ⟨3,false,14,24⟩ .empty) ⟨3,false,15,20⟩ .empty) ⟨3,false,15,28⟩ (.node (.node .empty ⟨3,false,16,17⟩ .empty) ⟨3,false,16,23⟩ .empty)))
def t100_124 : Tree := .node t100_112 ⟨3,false,12,24⟩ t113_124
def t125_137 : Tree := (.node (.node (.node (.node .empty ⟨3,false,16,31⟩ .empty) ⟨3,true,0,7⟩ (.node .empty ⟨3,true,0,21⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,2,15⟩ .empty) ⟨3,true,2,21⟩ .empty)) ⟨3,true,2,29⟩ (.node (.node (.node .empty ⟨3,true,3,3⟩ .empty) ⟨3,true,3,17⟩ .empty) ⟨3,true,3,23⟩ (.node (.node .empty ⟨3,true,3,31⟩ .empty) ⟨3,true,5,10⟩ .empty)))
def t138_149 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,21⟩ .empty) ⟨3,true,6,29⟩ .empty) ⟨3,true,7,11⟩ (.node (.node .empty ⟨3,true,7,17⟩ .empty) ⟨3,true,7,23⟩ .empty)) ⟨3,true,7,25⟩ (.node (.node (.node .empty ⟨3,true,7,31⟩ .empty) ⟨3,true,11,24⟩ .empty) ⟨3,true,12,15⟩ (.node (.node .empty ⟨3,true,12,21⟩ .empty) ⟨3,true,12,29⟩ .empty)))
def t125_149 : Tree := .node t125_137 ⟨3,true,5,24⟩ t138_149
def t100_149 : Tree := .node t100_124 ⟨3,false,16,25⟩ t125_149
def t150_162 : Tree := (.node (.node (.node (.node .empty ⟨3,true,13,17⟩ .empty) ⟨3,true,13,23⟩ (.node .empty ⟨3,true,13,25⟩ .empty)) ⟨3,true,13,31⟩ (.node (.node .empty ⟨4,false,0,19⟩ .empty) ⟨4,false,2,19⟩ .empty)) ⟨4,false,5,1⟩ (.node (.node (.node .empty ⟨4,false,5,2⟩ .empty) ⟨4,false,5,10⟩ .empty) ⟨4,false,5,16⟩ (.node (.node .empty ⟨4,false,5,22⟩ .empty) ⟨4,false,5,24⟩ .empty)))
def t163_174 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,19⟩ .empty) ⟨4,false,11,2⟩ .empty) ⟨4,false,11,10⟩ (.node (.node .empty ⟨4,false,11,16⟩ .empty) ⟨4,false,11,22⟩ .empty)) ⟨4,false,11,24⟩ (.node (.node (.node .empty ⟨4,false,11,30⟩ .empty) ⟨4,false,12,19⟩ .empty) ⟨4,true,1,6⟩ (.node (.node .empty ⟨4,true,1,20⟩ .empty) ⟨4,true,2,1⟩ .empty)))
def t150_174 : Tree := .node t150_162 ⟨4,false,5,30⟩ t163_174
def t175_186 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,10⟩ .empty) ⟨4,true,6,24⟩ .empty) ⟨4,true,9,14⟩ (.node (.node .empty ⟨4,true,9,20⟩ .empty) ⟨4,true,9,28⟩ .empty)) ⟨4,true,12,10⟩ (.node (.node (.node .empty ⟨4,true,12,24⟩ .empty) ⟨4,true,15,20⟩ .empty) ⟨4,true,15,28⟩ (.node (.node .empty ⟨5,true,0,8⟩ .empty) ⟨5,true,0,22⟩ .empty)))
def t187_198 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,16⟩ .empty) ⟨5,true,2,22⟩ .empty) ⟨5,true,2,30⟩ (.node (.node .empty ⟨5,true,5,11⟩ .empty) ⟨5,true,5,25⟩ .empty)) ⟨5,true,6,22⟩ (.node (.node (.node .empty ⟨5,true,6,30⟩ .empty) ⟨5,true,11,25⟩ .empty) ⟨5,true,12,16⟩ (.node (.node .empty ⟨5,true,12,22⟩ .empty) ⟨5,true,12,30⟩ .empty)))
def t175_198 : Tree := .node t175_186 ⟨5,true,1,3⟩ t187_198
def t150_198 : Tree := .node t150_174 ⟨4,true,6,2⟩ t175_198
def t100_198 : Tree := .node t100_149 ⟨3,true,13,11⟩ t150_198
def t0_198 : Tree := .node t0_99 ⟨3,false,8,1⟩ t100_198
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 9, 0, 5, 0, 0, 0, 6, 7, 15, 8, 11, 8, 0, 10, 0, 0, 0, 0, 12, 13, 9, 14, 5, 8, 0, 16, 0, 0, 0],#[0, 1, 3, 2, 11, 10, 4, 6, 5, 0, 0, 0, 8, 7, 0, 0, 9, 0, 0, 0, 25, 24, 12, 14, 13, 0, 0, 0, 16, 15, 0, 0, 17, 0, 18, 20, 19, 0, 0, 0, 22, 21, 0, 0, 23, 0, 32, 20, 25, 24, 26, 28, 27, 0, 0, 0, 30, 29, 0, 0, 31, 0, 32, 20, 19, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3),(true,13)],[(true,5)],[(false,6)],[(false,7),(false,8),(false,14)],[(true,2),(true,12)],[(false,9)],[(true,7)],[(true,11)],[(false,12)],[(false,13)],[(true,6)],[(false,15)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,3)],[(true,6)],[(false,6)],[(false,8)],[(true,2)],[(false,2)],[(false,11)],[(false,12)],[(true,11)],[(true,14)],[(false,14)],[(false,16)],[(false,17)],[(false,18),(false,32)],[(true,17),(true,23),(true,31)],[(true,20)],[(false,20)],[(false,22)],[(true,10),(true,24)],[(false,10),(false,24)],[(false,25)],[(false,26)],[(true,25)],[(true,28)],[(false,28)],[(false,30)],[(false,23),(false,31)]],
  t0_198⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_24 : t13_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,11,17⟩ = true := by decide
theorem check0_24 : t0_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_24
theorem check25_37 : t25_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check38_49 : t38_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node37 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,20⟩ = true := by decide
theorem check25_49 : t25_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node37 check25_37 check38_49
theorem node24 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,12,13⟩ = true := by decide
theorem check0_49 : t0_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node24 check0_24 check25_49
theorem check50_62 : t50_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check63_74 : t63_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node62 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,7,10⟩ = true := by decide
theorem check50_74 : t50_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node62 check50_62 check63_74
theorem check75_87 : t75_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check88_99 : t88_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,3⟩ = true := by decide
theorem check75_99 : t75_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check75_87 check88_99
theorem node74 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,13,1⟩ = true := by decide
theorem check50_99 : t50_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node74 check50_74 check75_99
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,28⟩ = true := by decide
theorem check0_99 : t0_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check0_49 check50_99
theorem check100_112 : t100_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check113_124 : t113_124.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node112 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,24⟩ = true := by decide
theorem check100_124 : t100_124.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node112 check100_112 check113_124
theorem check125_137 : t125_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check138_149 : t138_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,24⟩ = true := by decide
theorem check125_149 : t125_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check125_137 check138_149
theorem node124 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,16,25⟩ = true := by decide
theorem check100_149 : t100_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node124 check100_124 check125_149
theorem check150_162 : t150_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check163_174 : t163_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node162 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,5,30⟩ = true := by decide
theorem check150_174 : t150_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node162 check150_162 check163_174
theorem check175_186 : t175_186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check187_198 : t187_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node186 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check175_198 : t175_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node186 check175_186 check187_198
theorem node174 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,2⟩ = true := by decide
theorem check150_198 : t150_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node174 check150_174 check175_198
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,13,11⟩ = true := by decide
theorem check100_198 : t100_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check100_149 check150_198
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check0_198 : t0_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check0_99 check100_198
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_198
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M008
