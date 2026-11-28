import Raw40A0LABase
import SweepPumping
import ZipAuditCore
import SparseBlankDelay

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LA0REWitness
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

/-- The attaining original blank-tape machine for the six-hole A1=0LA family.
    Literal table: 1RB0LA_1RC0LF_0RD0RE_1LD1LA_0LB1RF_HHH0RC. F0 is the actual halt entry. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def witness : Machine := fun s => (table s).bind id

theorem witness_compatible : compatible table witness := by
  intro s t ht
  simp only [witness,ht,Option.bind_some,id_eq]

/-- The 22,168-step exact finite run is sliced into 44 consecutive
    independent primitive chunks. Every chunk is checked by Lean's kernel,
    not by trusting the external transcript generator. -/
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z2 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,true],[true,true,true]⟩
def z3 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true]⟩
def z4 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true]⟩
def z5 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z6 : Z0 := ⟨3,[false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z7 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z8 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true]⟩
def z9 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z10 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z11 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true]⟩
def z12 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true]⟩
def z13 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true]⟩
def z14 : Z0 := ⟨3,[true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z15 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true]⟩
def z16 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z17 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z18 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z19 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z20 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z21 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z22 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z23 : Z0 := ⟨3,[true,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z24 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z25 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true]⟩
def z26 : Z0 := ⟨0,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z27 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z28 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true]⟩
def z29 : Z0 := ⟨1,[true,true,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z30 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z31 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z32 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z33 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z34 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z35 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z36 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z37 : Z0 := ⟨5,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z38 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z39 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z40 : Z0 := ⟨2,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z41 : Z0 := ⟨3,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z42 : Z0 := ⟨1,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z43 : Z0 := ⟨3,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z44 : Z0 := ⟨5,[false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,true],[]⟩

theorem part0 : run0 table 512 z0 = some z1 := by decide +kernel
theorem part1 : run0 table 512 z1 = some z2 := by decide +kernel
theorem part2 : run0 table 512 z2 = some z3 := by decide +kernel
theorem part3 : run0 table 512 z3 = some z4 := by decide +kernel
theorem part4 : run0 table 512 z4 = some z5 := by decide +kernel
theorem part5 : run0 table 512 z5 = some z6 := by decide +kernel
theorem part6 : run0 table 512 z6 = some z7 := by decide +kernel
theorem part7 : run0 table 512 z7 = some z8 := by decide +kernel
theorem part8 : run0 table 512 z8 = some z9 := by decide +kernel
theorem part9 : run0 table 512 z9 = some z10 := by decide +kernel
theorem part10 : run0 table 512 z10 = some z11 := by decide +kernel
theorem part11 : run0 table 512 z11 = some z12 := by decide +kernel
theorem part12 : run0 table 512 z12 = some z13 := by decide +kernel
theorem part13 : run0 table 512 z13 = some z14 := by decide +kernel
theorem part14 : run0 table 512 z14 = some z15 := by decide +kernel
theorem part15 : run0 table 512 z15 = some z16 := by decide +kernel
theorem part16 : run0 table 512 z16 = some z17 := by decide +kernel
theorem part17 : run0 table 512 z17 = some z18 := by decide +kernel
theorem part18 : run0 table 512 z18 = some z19 := by decide +kernel
theorem part19 : run0 table 512 z19 = some z20 := by decide +kernel
theorem part20 : run0 table 512 z20 = some z21 := by decide +kernel
theorem part21 : run0 table 512 z21 = some z22 := by decide +kernel
theorem part22 : run0 table 512 z22 = some z23 := by decide +kernel
theorem part23 : run0 table 512 z23 = some z24 := by decide +kernel
theorem part24 : run0 table 512 z24 = some z25 := by decide +kernel
theorem part25 : run0 table 512 z25 = some z26 := by decide +kernel
theorem part26 : run0 table 512 z26 = some z27 := by decide +kernel
theorem part27 : run0 table 512 z27 = some z28 := by decide +kernel
theorem part28 : run0 table 512 z28 = some z29 := by decide +kernel
theorem part29 : run0 table 512 z29 = some z30 := by decide +kernel
theorem part30 : run0 table 512 z30 = some z31 := by decide +kernel
theorem part31 : run0 table 512 z31 = some z32 := by decide +kernel
theorem part32 : run0 table 512 z32 = some z33 := by decide +kernel
theorem part33 : run0 table 512 z33 = some z34 := by decide +kernel
theorem part34 : run0 table 512 z34 = some z35 := by decide +kernel
theorem part35 : run0 table 512 z35 = some z36 := by decide +kernel
theorem part36 : run0 table 512 z36 = some z37 := by decide +kernel
theorem part37 : run0 table 512 z37 = some z38 := by decide +kernel
theorem part38 : run0 table 512 z38 = some z39 := by decide +kernel
theorem part39 : run0 table 512 z39 = some z40 := by decide +kernel
theorem part40 : run0 table 512 z40 = some z41 := by decide +kernel
theorem part41 : run0 table 512 z41 = some z42 := by decide +kernel
theorem part42 : run0 table 512 z42 = some z43 := by decide +kernel
theorem part43 : run0 table 152 z43 = some z44 := by decide +kernel

theorem query : run0 table 22168 (project start) = some z44 := by
  have h := part0
  have h := join0 h part1
  have h := join0 h part2
  have h := join0 h part3
  have h := join0 h part4
  have h := join0 h part5
  have h := join0 h part6
  have h := join0 h part7
  have h := join0 h part8
  have h := join0 h part9
  have h := join0 h part10
  have h := join0 h part11
  have h := join0 h part12
  have h := join0 h part13
  have h := join0 h part14
  have h := join0 h part15
  have h := join0 h part16
  have h := join0 h part17
  have h := join0 h part18
  have h := join0 h part19
  have h := join0 h part20
  have h := join0 h part21
  have h := join0 h part22
  have h := join0 h part23
  have h := join0 h part24
  have h := join0 h part25
  have h := join0 h part26
  have h := join0 h part27
  have h := join0 h part28
  have h := join0 h part29
  have h := join0 h part30
  have h := join0 h part31
  have h := join0 h part32
  have h := join0 h part33
  have h := join0 h part34
  have h := join0 h part35
  have h := join0 h part36
  have h := join0 h part37
  have h := join0 h part38
  have h := join0 h part39
  have h := join0 h part40
  have h := join0 h part41
  have h := join0 h part42
  have h := join0 h part43
  have hn : (((((((((((((((((((((((((((((((((((((((((((512+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+512)+152) = 22168 := by omega
  simpa only [hn,z0,project,start] using h

theorem witness_halts : HaltsAfter witness 22168 := by
  have hz : (zrun table 22168 start).map project = some z44 :=
    (run_project table 22168 start).trans query
  cases h : zrun table 22168 start with
  | none => simp [h] at hz
  | some z =>
    have hproj : project z = z44 := by
      simpa only [h,Option.map_some,Option.some.injEq] using hz
    have H := zrun_sound table witness witness_compatible _ start z h
    rw [start_embed] at H
    have hread : readSlot (embed z) = (5,false) := by
      rw [read_embed]
      have e := congrArg (fun x : Z0 => (x.q,x.l.headD false)) hproj
      exact e.trans (by decide)
    constructor
    · rw [H]
      rfl
    · rw [run_append,H,Option.bind_some]
      change rawStep witness (embed z) = none
      rw [rawStep,hread]
      rfl

theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- Exact original six-hole A1=0LA parent, distinct from the global Raw40. -/
abbrev sixHoleParent : PartialMachine := BB6.Agent19Raw40.A0LA.p

theorem sixHole_compatible : compatible sixHoleParent witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : sixHoleParent (_,_) = none := by decide
      rw [h] at ht
      contradiction
    | cases ht <;> rfl

/-- No weighted upper bound below 22,169 can hold uniformly for A1=0LA.
    A complete complementary upper-bound proof is separately required. -/
theorem lower_sharp (B : Nat) (hB : B < 22169) :
    ∃ m : Machine, compatible sixHoleParent m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,sixHole_compatible,?_⟩
  intro hb
  have hn := hb 22168 0 witness_halts witness_delay
  omega

#print axioms query
#print axioms witness_halts
#print axioms lower_sharp
end BB6.Agent42Raw40A0LA0REWitness
