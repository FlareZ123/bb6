import Raw11Q0CombinedExtra
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Four-way source-normalized exact-complement interface to the *live* Raw11
152-cylinder frontier. This independently checks precise parent membership,
distinctness and the four removed rows, but intentionally receives the
four universal Cover proofs as explicit hypotheses. It never interprets a
candidate search tree or a failed CI job as a proof.
-/
namespace BB6.Agent47Raw11FourPending
open BB6Coverage BB6.Agent13BlankDelay

def pExtra28 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def pExtra132 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def pExtra140 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def pQ0Root53 : PartialMachine := fun (q,b) => match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def parents : List PartialMachine :=
  [pExtra28,pExtra132,pExtra140,pQ0Root53]

def prior : List PartialMachine := BB6.Agent47Raw11Q0CombinedExtra.remaining
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior parents

theorem literal_codes :
    parents.map BB6.Agent47PhaseFrontier.tableCode =
      [26318896606190888, 27874661676483464, 27872991061794760, 27873617542988488] := by decide +kernel

theorem codes_nodup :
    (parents.map BB6.Agent47PhaseFrontier.tableCode).Nodup := by decide +kernel

theorem all_members_in_152 :
    ∀ p ∈ parents, p ∈ prior := by
  intro p hp
  simp only [parents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> decide +kernel

theorem exact_census :
    (prior.length,remaining.length) = (152,148) := by decide +kernel

theorem raw11_cover_from_148 (B : Nat) (hB : 4663 ≤ B)
    (hParents : ∀ p ∈ parents, Cover (WeightedBound B) p)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Q0CombinedExtra.cover_from_remaining B hB
    (Q0RosterConsume.consume B prior parents hParents hRemaining)

#print axioms literal_codes
#print axioms codes_nodup
#print axioms all_members_in_152
#print axioms exact_census
#print axioms raw11_cover_from_148
end BB6.Agent47Raw11FourPending
