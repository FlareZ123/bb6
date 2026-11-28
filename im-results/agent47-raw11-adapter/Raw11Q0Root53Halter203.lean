import Q0ExhaustiveTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Explicit ordinary 203-step halter within the Raw11 q0-root53 five-hole
cylinder. This machine was found by a brute-force full-completion experiment
(25^5 = 9,765,625 tables), but neither the experiment nor a generated
trace is trusted: Lean's kernel decides the 202-step partial execution,
next unknown slot, and parent compatibility. A separate proof of the
universal 203-step *upper bound* is still needed for exact optimality.
-/
namespace BB6.Agent47Root53Halter203
open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree

def parent : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true  => some (some ⟨true,false,3⟩)
  | _,_ => none

/-- The only unspecified row is E0. Its completion by halt is the
concrete machine's halt transition. -/
def late : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true  => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true  => some (some ⟨true,false,3⟩)
  | 4,true  => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨false,true,1⟩)
  | _,_ => none

def machine : Machine := weightedTNFDefaultCompletion late
def at202 : FinRayCfg := (finitePartialRun late 202 finiteBlank).getD finiteBlank

theorem run202 : finitePartialRun late 202 finiteBlank = some at202 := by
  decide +kernel

theorem first_hole202 : late (readSlot (embedFinRay at202)) = none := by
  decide +kernel

theorem no_assigned_halt : weightedTNFNoAssignedHalt late := by
  decide +kernel

/-- 202 defined blank steps, followed by halt on the next (203rd) step. -/
theorem halts202 : HaltsAfter machine 202 := by
  apply (weightedTNF_halt_iff_firstHole late no_assigned_halt 202).mpr
  exact ⟨embedFinRay at202,
    Q0ExhaustiveTree.finite_known late 202 at202 run202, first_hole202⟩

theorem compatible_parent : compatible parent machine := by decide +kernel

theorem score203_halter :
    ∃ m, compatible parent m ∧ HaltsAfter m 202 :=
  ⟨machine, compatible_parent, halts202⟩

#print axioms halts202
#print axioms compatible_parent
#print axioms score203_halter
end BB6.Agent47Root53Halter203
