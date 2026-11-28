import ExactHalt
import WeightedFirstOneCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34Plan
open BB6Coverage BB6.Agent13BlankDelay

/-- Check the sparse delay bound at each halting leaf, instead of charging
the universal five-step normalization margin to all leaves. -/
def weightedCheck (B : Nat) (p : PartialMachine) : Cert → Bool
  | .halt n =>
      decide (p initialSlot = some (some ⟨true,true,1⟩)) &&
      finiteHaltCheck p n &&
      (possibleDelays p 0).all (fun d => decide (d+n+1 ≤ B))
  | c => certCheck 0 p c

theorem zeroCover_weighted (B : Nat) (p : PartialMachine)
    (h : Cover (DecidedBelow 0) p) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases h.sound m hm with hn | ⟨n,hn,_⟩
  · exact weighted_of_never B m hn
  · omega

theorem weightedCheck_sound (B : Nat) (p : PartialMachine) (cert : Cert)
    (h : weightedCheck B p cert = true) : Cover (WeightedBound B) p := by
  cases cert with
  | halt n =>
    have hh : (decide (p initialSlot = some (some ⟨true,true,1⟩)) = true ∧
        finiteHaltCheck p n = true) ∧
        (possibleDelays p 0).all (fun d => decide (d+n+1 ≤ B)) = true := by
      simpa only [weightedCheck,Bool.and_eq_true] using h
    exact weighted_halt_leaf p B n (of_decide_eq_true hh.1.1)
      (finiteHaltCheck_exact p n hh.1.2)
      (fun d hd => of_decide_eq_true (List.all_eq_true.mp hh.2 d hd))
  | side entry period right boundary =>
    exact zeroCover_weighted B p (cert_sound 0 p (.side entry period right boundary) h)
  | closed entry ss =>
    exact zeroCover_weighted B p (cert_sound 0 p (.closed entry ss) h)

theorem weightedPlan_closed (nodes : Array Node) (B fuel root : Nat)
    (p : PartialMachine) (h : checkWith nodes [] (weightedCheck B) fuel root p = true) :
    Cover (WeightedBound B) p := by
  apply checkWith_sound nodes [] (weightedCheck B) (weightedCheck_sound B) _ fuel root p h
  intro j row hj
  simp at hj

#print axioms weightedCheck_sound
#print axioms weightedPlan_closed
end BB6.Agent50Raw34Plan
