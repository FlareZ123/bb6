import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29FastZipWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

/-- Since there are six states, a simple incoming blank path has at most
    five edges. The expensive exact sparse delay enumeration is only needed
    when the proposed bound is within five of the executed transition count. -/
theorem weightOK_of_slack (p : PartialMachine) (s : Slot) (n B : Nat)
    (h : n + 6 ≤ B) : weightOK p s n B = true := by
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d hd
  have hd' : d < 6 := List.mem_range.mp (List.mem_filter.mp hd).1
  exact decide_eq_true (by omega)

def fastWeightOK (p : PartialMachine) (s : Slot) (n B : Nat) : Bool :=
  if n+6 ≤ B then true else weightOK p s n B

theorem fastWeightOK_eq (p : PartialMachine) (s : Slot) (n B : Nat) :
    fastWeightOK p s n B = weightOK p s n B := by
  unfold fastWeightOK
  split
  · exact (weightOK_of_slack p s n B (by assumption)).symm
  · rfl

def fastQueryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (zipRead p n = some s) && (decide (p s = none) && fastWeightOK p s n B)

theorem fastQueryOK_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastQueryOK B p n s = zipQueryOK B p n s := by
  simp only [fastQueryOK, zipQueryOK, fastWeightOK_eq]

def fastCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => fastQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => fastQueryOK B p n s &&
      allMoves (fun mv => fastCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    fastCheck B p t = zipCheck B p t := by
  induction t generalizing p with
  | last n s => simp only [fastCheck, zipCheck, fastQueryOK_eq]
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    simp only [fastCheck, zipCheck, fastQueryOK_eq, ih]

noncomputable def certifiedFast (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : fastCheck B p t = true) : WeightedTNFCertificate B p 6 :=
  certifiedZip B p t hroot hno ((fastCheck_eq B p t).symm.trans h)

/-- Split composition with all 24 physical moves explicit. The finite-state
    case split is proved once, rather than re-elaborated at every chunk. -/
theorem fastCheck_split24 (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (xs : List Audit) (hq : fastQueryOK B p n s = true)
    (h00 : fastCheck B (refine p s (some ⟨false,false,0⟩)) (byMove xs ⟨false,false,0⟩) = true)
    (h01 : fastCheck B (refine p s (some ⟨false,false,1⟩)) (byMove xs ⟨false,false,1⟩) = true)
    (h02 : fastCheck B (refine p s (some ⟨false,false,2⟩)) (byMove xs ⟨false,false,2⟩) = true)
    (h03 : fastCheck B (refine p s (some ⟨false,false,3⟩)) (byMove xs ⟨false,false,3⟩) = true)
    (h04 : fastCheck B (refine p s (some ⟨false,false,4⟩)) (byMove xs ⟨false,false,4⟩) = true)
    (h05 : fastCheck B (refine p s (some ⟨false,false,5⟩)) (byMove xs ⟨false,false,5⟩) = true)
    (h06 : fastCheck B (refine p s (some ⟨false,true,0⟩)) (byMove xs ⟨false,true,0⟩) = true)
    (h07 : fastCheck B (refine p s (some ⟨false,true,1⟩)) (byMove xs ⟨false,true,1⟩) = true)
    (h08 : fastCheck B (refine p s (some ⟨false,true,2⟩)) (byMove xs ⟨false,true,2⟩) = true)
    (h09 : fastCheck B (refine p s (some ⟨false,true,3⟩)) (byMove xs ⟨false,true,3⟩) = true)
    (h10 : fastCheck B (refine p s (some ⟨false,true,4⟩)) (byMove xs ⟨false,true,4⟩) = true)
    (h11 : fastCheck B (refine p s (some ⟨false,true,5⟩)) (byMove xs ⟨false,true,5⟩) = true)
    (h12 : fastCheck B (refine p s (some ⟨true,false,0⟩)) (byMove xs ⟨true,false,0⟩) = true)
    (h13 : fastCheck B (refine p s (some ⟨true,false,1⟩)) (byMove xs ⟨true,false,1⟩) = true)
    (h14 : fastCheck B (refine p s (some ⟨true,false,2⟩)) (byMove xs ⟨true,false,2⟩) = true)
    (h15 : fastCheck B (refine p s (some ⟨true,false,3⟩)) (byMove xs ⟨true,false,3⟩) = true)
    (h16 : fastCheck B (refine p s (some ⟨true,false,4⟩)) (byMove xs ⟨true,false,4⟩) = true)
    (h17 : fastCheck B (refine p s (some ⟨true,false,5⟩)) (byMove xs ⟨true,false,5⟩) = true)
    (h18 : fastCheck B (refine p s (some ⟨true,true,0⟩)) (byMove xs ⟨true,true,0⟩) = true)
    (h19 : fastCheck B (refine p s (some ⟨true,true,1⟩)) (byMove xs ⟨true,true,1⟩) = true)
    (h20 : fastCheck B (refine p s (some ⟨true,true,2⟩)) (byMove xs ⟨true,true,2⟩) = true)
    (h21 : fastCheck B (refine p s (some ⟨true,true,3⟩)) (byMove xs ⟨true,true,3⟩) = true)
    (h22 : fastCheck B (refine p s (some ⟨true,true,4⟩)) (byMove xs ⟨true,true,4⟩) = true)
    (h23 : fastCheck B (refine p s (some ⟨true,true,5⟩)) (byMove xs ⟨true,true,5⟩) = true)
    : fastCheck B p (.split n s (byMove xs)) = true := by
  simp only [fastCheck, Bool.and_eq_true]
  refine ⟨hq, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact h00
  · exact h06
  · exact h12
  · exact h18
  · exact h01
  · exact h07
  · exact h13
  · exact h19
  · exact h02
  · exact h08
  · exact h14
  · exact h20
  · exact h03
  · exact h09
  · exact h15
  · exact h21
  · exact h04
  · exact h10
  · exact h16
  · exact h22
  · exact h05
  · exact h11
  · exact h17
  · exact h23

#print axioms fastCheck_split24
#print axioms weightOK_of_slack
#print axioms fastCheck_eq
#print axioms certifiedFast
end BB6.Agent29FastZipWeight
