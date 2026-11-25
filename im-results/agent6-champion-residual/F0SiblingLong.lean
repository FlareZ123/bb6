import F0SiblingCover
import SweepPumping

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6F0.Long
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt

/-! Exact segmented replay of the three longer F0=1RC children.
    Each segment is independently reducible, and the balanced join tree
    avoids repeated evaluation of the long prefix. -/

namespace r9
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,2⟩ ⟨false,true,2⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨3,[true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,false,false,false,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,true]⟩
def z2 : Z0 := ⟨0,[false,true,false,true,false,true,false,false,true,false,true,true,true,true,false,false,true,false,true,false,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,true]⟩
def z3 : Z0 := ⟨3,[true,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,false,false,true,false,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,true,false,false,false,false,false,true]⟩
def z4 : Z0 := ⟨2,[false,true,true,true,true,false,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,false,false,true,true,true,true,false,true,false,true,true,true,true,false,true,false,false,false,false,false,true]⟩
def z5 : Z0 := ⟨4,[false,false,true,false,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,false,false,true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,false,true,false,true]⟩
def z6 : Z0 := ⟨0,[true,true,true,true,false,true,false,false,true,false,true,false,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,false,false,false,true,false,true,false,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 1024 z1 = some z2 := rfl
theorem seg2 : run0 p 1024 z2 = some z3 := rfl
theorem seg3 : run0 p 1024 z3 = some z4 := rfl
theorem seg4 : run0 p 1024 z4 = some z5 := rfl
theorem seg5 : run0 p 255 z5 = some z6 := rfl
theorem join_1_3 : run0 p 2048 z1 = some z3 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z1) (b := z2) (c := z3) seg1 seg2
theorem join_0_3 : run0 p 3072 z0 = some z3 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z0) (b := z1) (c := z3) seg0 join_1_3
theorem join_4_6 : run0 p 1279 z4 = some z6 :=
  join0 (p := p) (n := 1024) (k := 255) (a := z4) (b := z5) (c := z6) seg4 seg5
theorem join_3_6 : run0 p 2303 z3 = some z6 :=
  join0 (p := p) (n := 1024) (k := 1279) (a := z3) (b := z4) (c := z6) seg3 join_4_6
theorem join_0_6 : run0 p 5375 z0 = some z6 :=
  join0 (p := p) (n := 3072) (k := 2303) (a := z0) (b := z3) (c := z6) join_0_3 join_3_6
theorem checked : BB6.Agent48Parent.check p 5375 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 5375 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_6]
  decide
#print axioms checked
end r9

namespace r13
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,2⟩ ⟨false,true,3⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨0,[false,true,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,false,false,true,false,true,false,false,false,true,true,true]⟩
def z2 : Z0 := ⟨0,[true,true,false,true,true,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,true]⟩
theorem seg0 : run0 p 1024 z0 = some z1 := rfl
theorem seg1 : run0 p 264 z1 = some z2 := rfl
theorem join_0_2 : run0 p 1288 z0 = some z2 :=
  join0 (p := p) (n := 1024) (k := 264) (a := z0) (b := z1) (c := z2) seg0 seg1
theorem checked : BB6.Agent48Parent.check p 1288 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 1288 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_2]
  decide
#print axioms checked
end r13

namespace r15
def p : PartialMachine := BB6.Agent6F0.child ⟨true,true,2⟩ ⟨true,true,3⟩
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨2,[false,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,false,true,false,true,true,true,true,false,true,false,true]⟩
def z2 : Z0 := ⟨4,[true,false,false,true,false,true,false,false,true,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,true,false,true,false,true]⟩
def z3 : Z0 := ⟨5,[true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,false,true,false,true,false,false,false,false,false,true]⟩
def z4 : Z0 := ⟨3,[true,true,true,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,false,true,false,true,false,true,false,true,false,true]⟩
def z5 : Z0 := ⟨1,[false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,false,true,false,true,false,false,false,false,false,true]⟩
def z6 : Z0 := ⟨4,[true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,false,false,false,false,true,false,false,false,false,false,false,false,true]⟩
def z7 : Z0 := ⟨1,[false,true,true,true,false,true,false,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,false,false,false,false,false,false,false,false,false,true,false,true]⟩
def z8 : Z0 := ⟨4,[true,true,true,false,false,true,false,false,true,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[false,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true]⟩
def z9 : Z0 := ⟨5,[true,false,true,true,true,true,true,true,true,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,false,true,true,true,false,false,true,false,false,false,true,false,true,false,false,false,false,false,true]⟩
def z10 : Z0 := ⟨5,[false,false,true,false,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,false,false,false,true,false,true,false,false,false,true]⟩
def z11 : Z0 := ⟨4,[true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,false,true,true,true,false,false,false,false,true,false,false,false,true,false,false,false,true,false,true]⟩
def z12 : Z0 := ⟨2,[true,true,false,true,false,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[true,true,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true]⟩
def z13 : Z0 := ⟨4,[true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,true]⟩
def z14 : Z0 := ⟨3,[true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,false,false,false,true,false,true,true,true,false,false,true,false,true,false,false,false,true]⟩
def z15 : Z0 := ⟨3,[true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,false,false,false,false,false,true,true,true,false,false,true,false,true,false,true,false,true]⟩
def z16 : Z0 := ⟨3,[true,true,true,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[true,true,false,true,false,true,false,true,true,true,false,false,false,false,true,false,false,false,false,false,true]⟩
def z17 : Z0 := ⟨2,[false,true,false,true,false,false,true,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,false,true,true,true,false,false,false,false,true,false,true,false,false,false,true]⟩
def z18 : Z0 := ⟨0,[false,true,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,false,false,false,false,false,true,false,true]⟩
def z19 : Z0 := ⟨3,[true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,true,true,true,true,false,false,false,true,false,true,true,true,false,false,true,false,false,false,true,false,true,false,true]⟩
def z20 : Z0 := ⟨2,[false,true,true,true,true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,false,false,false,false,true,true,true,false,false,true,false,false,false,false,false,false,false,false,false,true]⟩
def z21 : Z0 := ⟨2,[false,true,true,true,true,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,false,true,false,true,true,true,false,false,false,false,false,false,true,false,false,false,false,false,true]⟩
def z22 : Z0 := ⟨4,[true,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[false,true,true,false,true,true,true,true,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,false,false,false,true]⟩
def z23 : Z0 := ⟨3,[true,true,true,true,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,false,true,false,false,false,true,false,false,false,true]⟩
def z24 : Z0 := ⟨5,[true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,false,true,true,true,true,false,true,false,false,false,true,true,true,false,false,true,false,true,false,true,false,true,false,false,false,true]⟩
def z25 : Z0 := ⟨3,[true,true,true,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,true,true,true],[false,false,true,false,true,false,false,false,false,false,true,false,true]⟩
def z26 : Z0 := ⟨2,[false,true,true,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,false,false,false,true,false,true,true,true,false,false,false,false,true,false,true,false,false,false,true,false,true]⟩
def z27 : Z0 := ⟨3,[false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[false,false,false,false,true,true,true,true,false,false,false,false,false,true,true,true,false,false,false,false,true,false,false,false,true,false,true,false,true]⟩
def z28 : Z0 := ⟨3,[true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,false,false,false,true,false,true,false,true,false,true]⟩
def z29 : Z0 := ⟨2,[false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[true,true,true,false,true,true,true,true,false,true,false,false,false,true,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true]⟩
def z30 : Z0 := ⟨3,[false,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true],[false,false,true,false,false,false,false,false,true,false,false,false,false,false,false,false,true]⟩
def z31 : Z0 := ⟨3,[true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true]⟩
def z32 : Z0 := ⟨2,[false,true,true,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,false,false,false,false,false,true,false,true,false,false,false,false,false,true]⟩
def z33 : Z0 := ⟨2,[true,true,false,false,true,false,true,false,false,true,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,false,false,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,false,false,false,false,true]⟩
def z34 : Z0 := ⟨4,[false,true,false,false,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,true,false,false,false,true,true,true,false,false,true,false,true,false,false,false,false,false,true,false,false,false,true]⟩
def z35 : Z0 := ⟨2,[false,true,true,true,true,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,false,false,true,false,true,false,false,false,true,false,false,false,true]⟩
def z36 : Z0 := ⟨4,[true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,false,true,true,true,true,false,true,false,false,false,true,true,true,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true]⟩
def z37 : Z0 := ⟨2,[true,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[true,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩
def z38 : Z0 := ⟨4,[false,false,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,true,false,true,true,true,true,false,false,false,true,false,true,true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,false,true]⟩
def z39 : Z0 := ⟨2,[true,true,false,false,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true],[false,false,false,false,false,true,true,true,false,false,true,false,false,false,true,false,false,false,false,false,true,false,true]⟩
def z40 : Z0 := ⟨2,[false,true,true,true,true,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,false,true,false,true,true,true,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true]⟩
def z41 : Z0 := ⟨3,[true,false,false,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,false,true,true,true,true,false,true,false,false,false,true,true,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true]⟩
def z42 : Z0 := ⟨4,[true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,false,true,true,true],[true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,false,false,true,false,true]⟩
def z43 : Z0 := ⟨4,[true,false,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,true,true,false,false,false,true,false,true,true,true,false,false,true,false,true,false,false,false,false,false,true,false,true,false,true]⟩
def z44 : Z0 := ⟨4,[false,false,true,false,true,false,false,true,false,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,false,false,false,false,false,false,true,true,true,false,false,true,false,true,false,true,false,false,false,true,false,true,false,true]⟩
def z45 : Z0 := ⟨2,[false,true,false,true,false,false,true,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,true,false,true,true,true,false,false,false,false,true,false,false,false,true,false,true,false,true,false,true]⟩
def z46 : Z0 := ⟨2,[false,true,false,true,false,false,true,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,false,false,true,true,true,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true]⟩
def z47 : Z0 := ⟨2,[false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true]⟩
def z48 : Z0 := ⟨4,[false,false,true,false,true,false,false,true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true],[false,false,false,false,false,true,false,true,true,true,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,true]⟩
def z49 : Z0 := ⟨0,[true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true,true,true],[false,true,true,true,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,true]⟩
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
theorem seg12 : run0 p 1024 z12 = some z13 := rfl
theorem seg13 : run0 p 1024 z13 = some z14 := rfl
theorem seg14 : run0 p 1024 z14 = some z15 := rfl
theorem seg15 : run0 p 1024 z15 = some z16 := rfl
theorem seg16 : run0 p 1024 z16 = some z17 := rfl
theorem seg17 : run0 p 1024 z17 = some z18 := rfl
theorem seg18 : run0 p 1024 z18 = some z19 := rfl
theorem seg19 : run0 p 1024 z19 = some z20 := rfl
theorem seg20 : run0 p 1024 z20 = some z21 := rfl
theorem seg21 : run0 p 1024 z21 = some z22 := rfl
theorem seg22 : run0 p 1024 z22 = some z23 := rfl
theorem seg23 : run0 p 1024 z23 = some z24 := rfl
theorem seg24 : run0 p 1024 z24 = some z25 := rfl
theorem seg25 : run0 p 1024 z25 = some z26 := rfl
theorem seg26 : run0 p 1024 z26 = some z27 := rfl
theorem seg27 : run0 p 1024 z27 = some z28 := rfl
theorem seg28 : run0 p 1024 z28 = some z29 := rfl
theorem seg29 : run0 p 1024 z29 = some z30 := rfl
theorem seg30 : run0 p 1024 z30 = some z31 := rfl
theorem seg31 : run0 p 1024 z31 = some z32 := rfl
theorem seg32 : run0 p 1024 z32 = some z33 := rfl
theorem seg33 : run0 p 1024 z33 = some z34 := rfl
theorem seg34 : run0 p 1024 z34 = some z35 := rfl
theorem seg35 : run0 p 1024 z35 = some z36 := rfl
theorem seg36 : run0 p 1024 z36 = some z37 := rfl
theorem seg37 : run0 p 1024 z37 = some z38 := rfl
theorem seg38 : run0 p 1024 z38 = some z39 := rfl
theorem seg39 : run0 p 1024 z39 = some z40 := rfl
theorem seg40 : run0 p 1024 z40 = some z41 := rfl
theorem seg41 : run0 p 1024 z41 = some z42 := rfl
theorem seg42 : run0 p 1024 z42 = some z43 := rfl
theorem seg43 : run0 p 1024 z43 = some z44 := rfl
theorem seg44 : run0 p 1024 z44 = some z45 := rfl
theorem seg45 : run0 p 1024 z45 = some z46 := rfl
theorem seg46 : run0 p 1024 z46 = some z47 := rfl
theorem seg47 : run0 p 1024 z47 = some z48 := rfl
theorem seg48 : run0 p 236 z48 = some z49 := rfl
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
theorem join_10_12 : run0 p 2048 z10 = some z12 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z10) (b := z11) (c := z12) seg10 seg11
theorem join_9_12 : run0 p 3072 z9 = some z12 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z9) (b := z10) (c := z12) seg9 join_10_12
theorem join_6_12 : run0 p 6144 z6 = some z12 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z6) (b := z9) (c := z12) join_6_9 join_9_12
theorem join_0_12 : run0 p 12288 z0 = some z12 :=
  join0 (p := p) (n := 6144) (k := 6144) (a := z0) (b := z6) (c := z12) join_0_6 join_6_12
theorem join_13_15 : run0 p 2048 z13 = some z15 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z13) (b := z14) (c := z15) seg13 seg14
theorem join_12_15 : run0 p 3072 z12 = some z15 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z12) (b := z13) (c := z15) seg12 join_13_15
theorem join_16_18 : run0 p 2048 z16 = some z18 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z16) (b := z17) (c := z18) seg16 seg17
theorem join_15_18 : run0 p 3072 z15 = some z18 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z15) (b := z16) (c := z18) seg15 join_16_18
theorem join_12_18 : run0 p 6144 z12 = some z18 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z12) (b := z15) (c := z18) join_12_15 join_15_18
theorem join_19_21 : run0 p 2048 z19 = some z21 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z19) (b := z20) (c := z21) seg19 seg20
theorem join_18_21 : run0 p 3072 z18 = some z21 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z18) (b := z19) (c := z21) seg18 join_19_21
theorem join_22_24 : run0 p 2048 z22 = some z24 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z22) (b := z23) (c := z24) seg22 seg23
theorem join_21_24 : run0 p 3072 z21 = some z24 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z21) (b := z22) (c := z24) seg21 join_22_24
theorem join_18_24 : run0 p 6144 z18 = some z24 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z18) (b := z21) (c := z24) join_18_21 join_21_24
theorem join_12_24 : run0 p 12288 z12 = some z24 :=
  join0 (p := p) (n := 6144) (k := 6144) (a := z12) (b := z18) (c := z24) join_12_18 join_18_24
theorem join_0_24 : run0 p 24576 z0 = some z24 :=
  join0 (p := p) (n := 12288) (k := 12288) (a := z0) (b := z12) (c := z24) join_0_12 join_12_24
theorem join_25_27 : run0 p 2048 z25 = some z27 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z25) (b := z26) (c := z27) seg25 seg26
theorem join_24_27 : run0 p 3072 z24 = some z27 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z24) (b := z25) (c := z27) seg24 join_25_27
theorem join_28_30 : run0 p 2048 z28 = some z30 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z28) (b := z29) (c := z30) seg28 seg29
theorem join_27_30 : run0 p 3072 z27 = some z30 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z27) (b := z28) (c := z30) seg27 join_28_30
theorem join_24_30 : run0 p 6144 z24 = some z30 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z24) (b := z27) (c := z30) join_24_27 join_27_30
theorem join_31_33 : run0 p 2048 z31 = some z33 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z31) (b := z32) (c := z33) seg31 seg32
theorem join_30_33 : run0 p 3072 z30 = some z33 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z30) (b := z31) (c := z33) seg30 join_31_33
theorem join_34_36 : run0 p 2048 z34 = some z36 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z34) (b := z35) (c := z36) seg34 seg35
theorem join_33_36 : run0 p 3072 z33 = some z36 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z33) (b := z34) (c := z36) seg33 join_34_36
theorem join_30_36 : run0 p 6144 z30 = some z36 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z30) (b := z33) (c := z36) join_30_33 join_33_36
theorem join_24_36 : run0 p 12288 z24 = some z36 :=
  join0 (p := p) (n := 6144) (k := 6144) (a := z24) (b := z30) (c := z36) join_24_30 join_30_36
theorem join_37_39 : run0 p 2048 z37 = some z39 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z37) (b := z38) (c := z39) seg37 seg38
theorem join_36_39 : run0 p 3072 z36 = some z39 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z36) (b := z37) (c := z39) seg36 join_37_39
theorem join_40_42 : run0 p 2048 z40 = some z42 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z40) (b := z41) (c := z42) seg40 seg41
theorem join_39_42 : run0 p 3072 z39 = some z42 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z39) (b := z40) (c := z42) seg39 join_40_42
theorem join_36_42 : run0 p 6144 z36 = some z42 :=
  join0 (p := p) (n := 3072) (k := 3072) (a := z36) (b := z39) (c := z42) join_36_39 join_39_42
theorem join_43_45 : run0 p 2048 z43 = some z45 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z43) (b := z44) (c := z45) seg43 seg44
theorem join_42_45 : run0 p 3072 z42 = some z45 :=
  join0 (p := p) (n := 1024) (k := 2048) (a := z42) (b := z43) (c := z45) seg42 join_43_45
theorem join_45_47 : run0 p 2048 z45 = some z47 :=
  join0 (p := p) (n := 1024) (k := 1024) (a := z45) (b := z46) (c := z47) seg45 seg46
theorem join_47_49 : run0 p 1260 z47 = some z49 :=
  join0 (p := p) (n := 1024) (k := 236) (a := z47) (b := z48) (c := z49) seg47 seg48
theorem join_45_49 : run0 p 3308 z45 = some z49 :=
  join0 (p := p) (n := 2048) (k := 1260) (a := z45) (b := z47) (c := z49) join_45_47 join_47_49
theorem join_42_49 : run0 p 6380 z42 = some z49 :=
  join0 (p := p) (n := 3072) (k := 3308) (a := z42) (b := z45) (c := z49) join_42_45 join_45_49
theorem join_36_49 : run0 p 12524 z36 = some z49 :=
  join0 (p := p) (n := 6144) (k := 6380) (a := z36) (b := z42) (c := z49) join_36_42 join_42_49
theorem join_24_49 : run0 p 24812 z24 = some z49 :=
  join0 (p := p) (n := 12288) (k := 12524) (a := z24) (b := z36) (c := z49) join_24_36 join_36_49
theorem join_0_49 : run0 p 49388 z0 = some z49 :=
  join0 (p := p) (n := 24576) (k := 24812) (a := z0) (b := z24) (c := z49) join_0_24 join_24_49
theorem checked : BB6.Agent48Parent.check p 49388 (0,true) = true := by
  unfold BB6.Agent48Parent.check
  change decide ((run0 p 49388 z0).map BB6.Agent48Parent.slot0 = some (0,true)) = true
  rw [join_0_49]
  decide
#print axioms checked
end r15

theorem ordinary_oneRC (B : Nat) (hB : 49394 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (BB6.Agent6F0.child ⟨true,true,2⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.short_child B _ _ 638 (by omega) (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 638 (by omega) (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 638 (by omega) (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 638 (by omega) (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,432,64,432,256,4096],[4096,432,32,432,256,16,4096,432,32,432,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,306,64,434,256,4096],[4096,2,32,434,256,16,4096,2,32,306,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,32,32,432,256,16,4096,304,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,432,64,432,256,4096],[4096,128,32,432,256,16,4096,128,32,432,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,4528,32,432,256,16,4096,256,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 5375 (by omega) r9.checked
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,4400,32,432,256,16,4096,16,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,256,32,432,256,16,4096,256,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,432,64,432,256,4096],[4096,128,32,432,256,16,4096,432,32,432,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 1288 (by omega) r13.checked
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,4096,32,432,256,16,4096,304,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.short_child B _ _ 49388 (by omega) r15.checked
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,432,32,432,256,16,4096,304,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,16,32,432,256,16,4096,16,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,304,32,432,256,16,4096,32,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,1328,64,1456,256,4096],[4096,1024,32,1456,256,16,4096,1024,32,1328,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,432,64,432,256,4096],[4096,432,32,432,256,16,4096,128,32,432,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,32,32,432,256,16,4096,32,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,304,64,432,256,4096],[4096,32,32,432,256,16,4096,256,32,304,256,16,4096],4100⟩ (by decide)
  · exact BB6.Agent6F0.far_child B _ _ ⟨0,[0,1,0,1],[128,256,4096,64,128,256,128,256,2352,64,2480,256,4096],[4096,2048,32,2480,256,16,4096,2048,32,2352,256,16,4096],4100⟩ (by decide)

theorem cover_oneRC (B : Nat) (hB : 49394 ≤ B) :
    Cover (WeightedBound B) (BB6.Agent6F0.parent ⟨true,true,2⟩) :=
  BB6.Agent6F0.all_children B _ 637 (by omega) (by decide) (ordinary_oneRC B hB)
#print axioms cover_oneRC
end BB6.Agent6F0.Long
