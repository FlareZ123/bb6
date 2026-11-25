import F0SiblingCover
import SweepPumping
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48REReplay
open BB6Coverage BB6Coverage.Agent31Pump

namespace parent
def p : PartialMachine := BB6.Agent6F0.parent ⟨true,true,4⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨1,[true,true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 80 z6 = some z7 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_3_5 : run0 p 2048 z3 = some z5 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z3) (b := z4) (c := z5) seg3 seg4
theorem join_5_7 : run0 p 1104 z5 = some z7 :=
  join0 (p := p) (n := 1024) (k := 80) (a := z5) (b := z6) (c := z7) seg5 seg6
theorem join_3_7 : run0 p 3152 z3 = some z7 :=
  join0 (p := p) (n := 2048) (k := 1104) (a := z3) (b := z5) (c := z7) join_3_5 join_5_7
theorem join_0_7 : run0 p 6224 z0 = some z7 :=
  join0 (p := p) (n := 3072) (k := 3152) (a := z0) (b := z3) (c := z7) join_0_3 join_3_7
theorem checked : BB6.Agent48Parent.check p 6224 (1,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 6224 z0).map BB6.Agent48Parent.slot0 = some (1,true)) = true
  rw [join_0_7]
  decide
#print axioms checked
end parent

namespace r0
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,4⟩ ⟨false,false,0⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨0,[true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 81 z6 = some z7 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_3_5 : run0 p 2048 z3 = some z5 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z3) (b := z4) (c := z5) seg3 seg4
theorem join_5_7 : run0 p 1105 z5 = some z7 :=
  join0 (p := p) (n := 1024) (k := 81) (a := z5) (b := z6) (c := z7) seg5 seg6
theorem join_3_7 : run0 p 3153 z3 = some z7 :=
  join0 (p := p) (n := 2048) (k := 1105) (a := z3) (b := z5) (c := z7) join_3_5 join_5_7
theorem join_0_7 : run0 p 6225 z0 = some z7 :=
  join0 (p := p) (n := 3072) (k := 3153) (a := z0) (b := z3) (c := z7) join_0_3 join_3_7
theorem checked : BB6.Agent48Parent.check p 6225 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 6225 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_7]
  decide
#print axioms checked
end r0

namespace r1
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,4⟩ ⟨false,true,0⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨0,[true,false,true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 81 z6 = some z7 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_3_5 : run0 p 2048 z3 = some z5 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z3) (b := z4) (c := z5) seg3 seg4
theorem join_5_7 : run0 p 1105 z5 = some z7 :=
  join0 (p := p) (n := 1024) (k := 81) (a := z5) (b := z6) (c := z7) seg5 seg6
theorem join_3_7 : run0 p 3153 z3 = some z7 :=
  join0 (p := p) (n := 2048) (k := 1105) (a := z3) (b := z5) (c := z7) join_3_5 join_5_7
theorem join_0_7 : run0 p 6225 z0 = some z7 :=
  join0 (p := p) (n := 3072) (k := 3153) (a := z0) (b := z3) (c := z7) join_0_3 join_3_7
theorem checked : BB6.Agent48Parent.check p 6225 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 6225 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_7]
  decide
#print axioms checked
end r1

namespace r2
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,4⟩ ⟨true,false,0⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨0,[true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 81 z6 = some z7 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_3_5 : run0 p 2048 z3 = some z5 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z3) (b := z4) (c := z5) seg3 seg4
theorem join_5_7 : run0 p 1105 z5 = some z7 :=
  join0 (p := p) (n := 1024) (k := 81) (a := z5) (b := z6) (c := z7) seg5 seg6
theorem join_3_7 : run0 p 3153 z3 = some z7 :=
  join0 (p := p) (n := 2048) (k := 1105) (a := z3) (b := z5) (c := z7) join_3_5 join_5_7
theorem join_0_7 : run0 p 6225 z0 = some z7 :=
  join0 (p := p) (n := 3072) (k := 3153) (a := z0) (b := z3) (c := z7) join_0_3 join_3_7
theorem checked : BB6.Agent48Parent.check p 6225 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 6225 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_7]
  decide
#print axioms checked
end r2

namespace r3
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,4⟩ ⟨true,true,0⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨0,[true,true,true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 81 z6 = some z7 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_3_5 : run0 p 2048 z3 = some z5 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z3) (b := z4) (c := z5) seg3 seg4
theorem join_5_7 : run0 p 1105 z5 = some z7 :=
  join0 (p := p) (n := 1024) (k := 81) (a := z5) (b := z6) (c := z7) seg5 seg6
theorem join_3_7 : run0 p 3153 z3 = some z7 :=
  join0 (p := p) (n := 2048) (k := 1105) (a := z3) (b := z5) (c := z7) join_3_5 join_5_7
theorem join_0_7 : run0 p 6225 z0 = some z7 :=
  join0 (p := p) (n := 3072) (k := 3153) (a := z0) (b := z3) (c := z7) join_0_3 join_3_7
theorem checked : BB6.Agent48Parent.check p 6225 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 6225 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_7]
  decide
#print axioms checked
end r3

namespace r9
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,4⟩ ⟨false,true,2⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨4,[true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z2 : Z0 := ⟨4,[true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,true,false,false,true,true,true]⟩
def z3 : Z0 := ⟨3,[false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z4 : Z0 := ⟨3,[true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false,true,true,true]⟩
def z5 : Z0 := ⟨5,[true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z6 : Z0 := ⟨1,[false,true,true],[true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z7 : Z0 := ⟨3,[true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z8 : Z0 := ⟨5,[true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,false,false,true,false,false,true,true,false,true,false,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z9 : Z0 := ⟨2,[true,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,true,false,true,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z10 : Z0 := ⟨2,[false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,true,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z11 : Z0 := ⟨2,[true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z12 : Z0 := ⟨0,[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,false,false,true,false,false,false,false,true,true,false,true,false,false,false,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true]⟩
def z13 : Z0 := ⟨0,[true,true,true,true,false,true,true,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,false,false,true,false,false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 1024 z5 = some z6 := rfl
theorem seg6 : run0 p 1024 z6 = some z7 := rfl
theorem seg7 : run0 p 1024 z7 = some z8 := rfl
theorem seg8 : run0 p 1024 z8 = some z9 := rfl
theorem seg9 : run0 p 1024 z9 = some z10 := rfl
theorem seg10 : run0 p 1024 z10 = some z11 := rfl
theorem seg11 : run0 p 1024 z11 = some z12 := rfl
theorem seg12 : run0 p 194 z12 = some z13 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_4_6 : run0 p 2048 z4 = some z6 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z4) (b := z5) (c := z6) seg4 seg5
theorem join_3_6 : run0 p 3072 z3 = some z6 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z3) (b := z4) (c := z6) seg3 join_4_6
theorem join_0_6 : run0 p 6144 z0 = some z6 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z0) (b := z3) (c := z6) join_0_3 join_3_6
theorem join_7_9 : run0 p 2048 z7 = some z9 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z7) (b := z8) (c := z9) seg7 seg8
theorem join_6_9 : run0 p 3072 z6 = some z9 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z6) (b := z7) (c := z9) seg6 join_7_9
theorem join_9_11 : run0 p 2048 z9 = some z11 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z9) (b := z10) (c := z11) seg9 seg10
theorem join_11_13 : run0 p 1218 z11 = some z13 :=
  join0 (p := p) (n := 1024) (k := 194) (a := z11) (b := z12) (c := z13) seg11 seg12
theorem join_9_13 : run0 p 3266 z9 = some z13 :=
  join0 (p := p) (n := 2048) (k := 1218) (a := z9) (b := z11) (c := z13) join_9_11 join_11_13
theorem join_6_13 : run0 p 6338 z6 = some z13 :=
  join0 (p := p) (n := 3072) (k := 3266) (a := z6) (b := z9) (c := z13) join_6_9 join_9_13
theorem join_0_13 : run0 p 12482 z0 = some z13 :=
  join0 (p := p) (n := 6144) (k := 6338) (a := z0) (b := z6) (c := z13) join_0_6 join_6_13
theorem checked : BB6.Agent48Parent.check p 12482 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 12482 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_13]
  decide
#print axioms checked
end r9

end BB6.Agent48REReplay
