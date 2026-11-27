import Raw40A0LA1LC66Macros
import CrossingSource

namespace BB6.Agent19Raw40.Leaf66Entry
open BB6Coverage BB6Coverage.Agent50Zipper
open Leaf66Macros
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- Literal checkpoints of original-table execution, independently kernel
-- reduced in bounded 2048-step chunks. No untrusted evaluator in the proof.
def z0 : Z := ⟨0,0,[],[]⟩
def z1 : Z := ⟨2,-2,[true,true,false,true,false,true],[true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true]⟩
def z2 : Z := ⟨0,8,[true,true,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true],[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,true,true,true,false,false,false,true,true,true]⟩
def z3 : Z := ⟨2,-2,[true,true,false,true,true,true,true],[true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,true,true,true,false,false,false,true,true,true]⟩
def z4 : Z := ⟨1,8,[false,true,true,true,true,true,true,false,false,true,true,true,true,false,true,true,false,true],[false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,false,false,false,true,true,true]⟩
def z5 : Z := ⟨3,32,[false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,false,true,false,true,true,true],[false,false,false,true,true,true,false,false,true,true,false,false,false,true,true,true]⟩
def z6 : Z := ⟨5,8,[true,false,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z7 : Z := ⟨5,8,[true,true,true,true,true,false,false,true,false,true,false,true,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z8 : Z := ⟨5,8,[true,true,false,false,true,false,true,true,false,true,true,true,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z9 : Z := ⟨0,8,[true,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,false,true],[false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z10 : Z := ⟨3,8,[false,false,true,true,false,true,false,true,true,true,true,false,true,true,true,false,true,false,true],[false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z11 : Z := ⟨0,12,[false,true,true,true,true,true,true,false,false,true,true,true,false,true,false,true,false,true,false,true,true,false,true],[false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z12 : Z := ⟨2,30,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,false,true,false,true,true,false,true,true,false,true],[true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z13 : Z := ⟨2,6,[true,true,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z14 : Z := ⟨3,4,[true,false,true,false,true,true,false,true,true,false,true,true,true,false,true],[true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z15 : Z := ⟨5,14,[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,true,false,true],[true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true]⟩
def z16 : Z := ⟨3,6,[true,false,false,true,true,true,false,true,false,true,false,true,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z17 : Z := ⟨2,18,[true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z18 : Z := ⟨5,10,[true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,true,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z19 : Z := ⟨3,14,[false,false,true,true,true,true,true,true,true,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true],[false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z20 : Z := ⟨2,18,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true],[true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z21 : Z := ⟨2,16,[true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,true,false,true,false,true,false,true,true,true],[true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z22 : Z := ⟨2,6,[true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,true,true],[true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z23 : Z := ⟨0,10,[true,true,true,true,true,true,true,false,false,true,false,true,true,true,true,true,true,false,true,true,true],[false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z24 : Z := ⟨3,-2,[true,false,true,true,false,true,true,true,true],[true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z25 : Z := ⟨0,6,[true,false,false,true,false,true,false,true,false,true,false,true,true,true,true,true,true],[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,true,true,true]⟩
def z26 : Z := ⟨5,16,[true,true,true,true,true,true,true,true,true,false,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true],[false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z27 : Z := ⟨2,6,[false,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z28 : Z := ⟨1,22,[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,true,false,true,false,true,false,true],[false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z29 : Z := ⟨3,8,[false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true],[false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z30 : Z := ⟨2,6,[true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z31 : Z := ⟨2,4,[true,false,false,true,false,true,true,false,true,false,true,false,true,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z32 : Z := ⟨5,8,[true,true,true,true,false,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true],[true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z33 : Z := ⟨3,4,[true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true],[true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z34 : Z := ⟨0,8,[false,true,true,true,true,true,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z35 : Z := ⟨2,4,[true,true,false,true,false,true,false,true,false,true,true,true,true,true,false,true],[true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,true,true,true]⟩
def z36 : Z := ⟨5,12,[true,true,true,true,true,true,true,false,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,true],[true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z37 : Z := ⟨2,6,[true,true,false,false,true,true,false,true,false,true,false,true,true,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z38 : Z := ⟨4,2,[true,false,true,true,true,true,true,true,true,false,true,false,true,true],[true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z39 : Z := ⟨2,0,[true,false,false,true,true,true,false,true,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z40 : Z := ⟨0,10,[false,true,true,true,true,true,false,false,true,true,false,true,false,true,false,true,true,true,true,false,true,true],[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z41 : Z := ⟨2,4,[true,true,true,false,true,false,true,true,false,true,false,true,false,true,true,true],[true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z42 : Z := ⟨2,14,[true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,true,false,true,false,true,true,false,true,true,true],[true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z43 : Z := ⟨5,14,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true],[true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z44 : Z := ⟨0,4,[false,false,true,false,true,false,true,false,true,true,true,false,true,true,true,true],[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z45 : Z := ⟨2,-2,[true,false,true,false,true,true,true,true,true,true],[true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,true,true,true]⟩
def z46 : Z := ⟨0,10,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩

theorem s1 : zrun table 2048 z0 = some z1 := by decide +kernel
theorem p1 : zrun table 2048 z0 = some z1 := s1
theorem s2 : zrun table 2048 z1 = some z2 := by decide +kernel
theorem p2 : zrun table 4096 z0 = some z2 := BB6Coverage.Agent50Zipper.join p1 s2
theorem s3 : zrun table 2048 z2 = some z3 := by decide +kernel
theorem p3 : zrun table 6144 z0 = some z3 := BB6Coverage.Agent50Zipper.join p2 s3
theorem s4 : zrun table 2048 z3 = some z4 := by decide +kernel
theorem p4 : zrun table 8192 z0 = some z4 := BB6Coverage.Agent50Zipper.join p3 s4
theorem s5 : zrun table 2048 z4 = some z5 := by decide +kernel
theorem p5 : zrun table 10240 z0 = some z5 := BB6Coverage.Agent50Zipper.join p4 s5
theorem s6 : zrun table 2048 z5 = some z6 := by decide +kernel
theorem p6 : zrun table 12288 z0 = some z6 := BB6Coverage.Agent50Zipper.join p5 s6
theorem s7 : zrun table 2048 z6 = some z7 := by decide +kernel
theorem p7 : zrun table 14336 z0 = some z7 := BB6Coverage.Agent50Zipper.join p6 s7
theorem s8 : zrun table 2048 z7 = some z8 := by decide +kernel
theorem p8 : zrun table 16384 z0 = some z8 := BB6Coverage.Agent50Zipper.join p7 s8
theorem s9 : zrun table 2048 z8 = some z9 := by decide +kernel
theorem p9 : zrun table 18432 z0 = some z9 := BB6Coverage.Agent50Zipper.join p8 s9
theorem s10 : zrun table 2048 z9 = some z10 := by decide +kernel
theorem p10 : zrun table 20480 z0 = some z10 := BB6Coverage.Agent50Zipper.join p9 s10
theorem s11 : zrun table 2048 z10 = some z11 := by decide +kernel
theorem p11 : zrun table 22528 z0 = some z11 := BB6Coverage.Agent50Zipper.join p10 s11
theorem s12 : zrun table 2048 z11 = some z12 := by decide +kernel
theorem p12 : zrun table 24576 z0 = some z12 := BB6Coverage.Agent50Zipper.join p11 s12
theorem s13 : zrun table 2048 z12 = some z13 := by decide +kernel
theorem p13 : zrun table 26624 z0 = some z13 := BB6Coverage.Agent50Zipper.join p12 s13
theorem s14 : zrun table 2048 z13 = some z14 := by decide +kernel
theorem p14 : zrun table 28672 z0 = some z14 := BB6Coverage.Agent50Zipper.join p13 s14
theorem s15 : zrun table 2048 z14 = some z15 := by decide +kernel
theorem p15 : zrun table 30720 z0 = some z15 := BB6Coverage.Agent50Zipper.join p14 s15
theorem s16 : zrun table 2048 z15 = some z16 := by decide +kernel
theorem p16 : zrun table 32768 z0 = some z16 := BB6Coverage.Agent50Zipper.join p15 s16
theorem s17 : zrun table 2048 z16 = some z17 := by decide +kernel
theorem p17 : zrun table 34816 z0 = some z17 := BB6Coverage.Agent50Zipper.join p16 s17
theorem s18 : zrun table 2048 z17 = some z18 := by decide +kernel
theorem p18 : zrun table 36864 z0 = some z18 := BB6Coverage.Agent50Zipper.join p17 s18
theorem s19 : zrun table 2048 z18 = some z19 := by decide +kernel
theorem p19 : zrun table 38912 z0 = some z19 := BB6Coverage.Agent50Zipper.join p18 s19
theorem s20 : zrun table 2048 z19 = some z20 := by decide +kernel
theorem p20 : zrun table 40960 z0 = some z20 := BB6Coverage.Agent50Zipper.join p19 s20
theorem s21 : zrun table 2048 z20 = some z21 := by decide +kernel
theorem p21 : zrun table 43008 z0 = some z21 := BB6Coverage.Agent50Zipper.join p20 s21
theorem s22 : zrun table 2048 z21 = some z22 := by decide +kernel
theorem p22 : zrun table 45056 z0 = some z22 := BB6Coverage.Agent50Zipper.join p21 s22
theorem s23 : zrun table 2048 z22 = some z23 := by decide +kernel
theorem p23 : zrun table 47104 z0 = some z23 := BB6Coverage.Agent50Zipper.join p22 s23
theorem s24 : zrun table 2048 z23 = some z24 := by decide +kernel
theorem p24 : zrun table 49152 z0 = some z24 := BB6Coverage.Agent50Zipper.join p23 s24
theorem s25 : zrun table 2048 z24 = some z25 := by decide +kernel
theorem p25 : zrun table 51200 z0 = some z25 := BB6Coverage.Agent50Zipper.join p24 s25
theorem s26 : zrun table 2048 z25 = some z26 := by decide +kernel
theorem p26 : zrun table 53248 z0 = some z26 := BB6Coverage.Agent50Zipper.join p25 s26
theorem s27 : zrun table 2048 z26 = some z27 := by decide +kernel
theorem p27 : zrun table 55296 z0 = some z27 := BB6Coverage.Agent50Zipper.join p26 s27
theorem s28 : zrun table 2048 z27 = some z28 := by decide +kernel
theorem p28 : zrun table 57344 z0 = some z28 := BB6Coverage.Agent50Zipper.join p27 s28
theorem s29 : zrun table 2048 z28 = some z29 := by decide +kernel
theorem p29 : zrun table 59392 z0 = some z29 := BB6Coverage.Agent50Zipper.join p28 s29
theorem s30 : zrun table 2048 z29 = some z30 := by decide +kernel
theorem p30 : zrun table 61440 z0 = some z30 := BB6Coverage.Agent50Zipper.join p29 s30
theorem s31 : zrun table 2048 z30 = some z31 := by decide +kernel
theorem p31 : zrun table 63488 z0 = some z31 := BB6Coverage.Agent50Zipper.join p30 s31
theorem s32 : zrun table 2048 z31 = some z32 := by decide +kernel
theorem p32 : zrun table 65536 z0 = some z32 := BB6Coverage.Agent50Zipper.join p31 s32
theorem s33 : zrun table 2048 z32 = some z33 := by decide +kernel
theorem p33 : zrun table 67584 z0 = some z33 := BB6Coverage.Agent50Zipper.join p32 s33
theorem s34 : zrun table 2048 z33 = some z34 := by decide +kernel
theorem p34 : zrun table 69632 z0 = some z34 := BB6Coverage.Agent50Zipper.join p33 s34
theorem s35 : zrun table 2048 z34 = some z35 := by decide +kernel
theorem p35 : zrun table 71680 z0 = some z35 := BB6Coverage.Agent50Zipper.join p34 s35
theorem s36 : zrun table 2048 z35 = some z36 := by decide +kernel
theorem p36 : zrun table 73728 z0 = some z36 := BB6Coverage.Agent50Zipper.join p35 s36
theorem s37 : zrun table 2048 z36 = some z37 := by decide +kernel
theorem p37 : zrun table 75776 z0 = some z37 := BB6Coverage.Agent50Zipper.join p36 s37
theorem s38 : zrun table 2048 z37 = some z38 := by decide +kernel
theorem p38 : zrun table 77824 z0 = some z38 := BB6Coverage.Agent50Zipper.join p37 s38
theorem s39 : zrun table 2048 z38 = some z39 := by decide +kernel
theorem p39 : zrun table 79872 z0 = some z39 := BB6Coverage.Agent50Zipper.join p38 s39
theorem s40 : zrun table 2048 z39 = some z40 := by decide +kernel
theorem p40 : zrun table 81920 z0 = some z40 := BB6Coverage.Agent50Zipper.join p39 s40
theorem s41 : zrun table 2048 z40 = some z41 := by decide +kernel
theorem p41 : zrun table 83968 z0 = some z41 := BB6Coverage.Agent50Zipper.join p40 s41
theorem s42 : zrun table 2048 z41 = some z42 := by decide +kernel
theorem p42 : zrun table 86016 z0 = some z42 := BB6Coverage.Agent50Zipper.join p41 s42
theorem s43 : zrun table 2048 z42 = some z43 := by decide +kernel
theorem p43 : zrun table 88064 z0 = some z43 := BB6Coverage.Agent50Zipper.join p42 s43
theorem s44 : zrun table 2048 z43 = some z44 := by decide +kernel
theorem p44 : zrun table 90112 z0 = some z44 := BB6Coverage.Agent50Zipper.join p43 s44
theorem s45 : zrun table 2048 z44 = some z45 := by decide +kernel
theorem p45 : zrun table 92160 z0 = some z45 := BB6Coverage.Agent50Zipper.join p44 s45
theorem s46 : zrun table 1700 z45 = some z46 := by decide +kernel
theorem p46 : zrun table 93860 z0 = some z46 := BB6Coverage.Agent50Zipper.join p45 s46
abbrev entryZ : Z := z46
theorem entryRun : zrun table 93860 ⟨0,0,[],[]⟩ = some entryZ := p46

#print axioms entryRun
end BB6.Agent19Raw40.Leaf66Entry
