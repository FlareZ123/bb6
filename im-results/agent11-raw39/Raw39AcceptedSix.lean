import Raw39SemanticChunks
import Raw39Data
import Raw39B0RBData
import Raw39B1RCData
import Raw39B0REData
import Raw39RCData
import Raw39LAComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39AcceptedSix
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent11SemanticChunks BB6Coverage.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev child (mv : Move) := refine p39 (0,true) (some mv)

def remaining : List Move := [⟨false,false,4⟩, ⟨true,false,0⟩,
  ⟨true,false,1⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

theorem remaining_count : remaining.length = 5 := by decide

private theorem lift {A B : Nat} {m : Machine} (h : A ≤ B)
    (hb : WeightedBound A m) : WeightedBound B m :=
  fun k d hk hd => Nat.le_trans (hb k d hk hd) h

private theorem query_mono {A B : Nat} {p : PartialMachine} {n : Nat} {s : Slot}
    (hle : A ≤ B) (h : zipQueryOK A p n s = true) : zipQueryOK B p n s = true := by
  unfold zipQueryOK at *
  simp only [Bool.and_eq_true] at *
  refine ⟨h.1, h.2.1, ?_⟩
  unfold weightOK
  apply List.all_eq_true.mpr
  intro d hd
  exact decide_eq_true (Nat.le_trans (weightOK_sound p s n A h.2.2 d hd) hle)

private theorem cyc (B : Nat) (mv : Move) (e k : Nat) (r : Bool) (b : Int)
    (hk : 0 < k) (hc : zipCycle (child mv) e k r b = true) : Bound B (child mv) :=
  fun m hm => weighted_never B m (zipCycle_sound (child mv) e k r b hk hc m hm)

/-- Six accepted child bounds and nine literal cycles leave just five canonical
A1 child obligations. Fresh E/F symmetry is supplied by the original TNF theorem. -/
theorem parent_bound_five (B : Nat) (hB : 2354 ≤ B)
    (h : ∀ mv ∈ remaining, Bound B (child mv)) : Bound B p39 := by
  apply join_normalized B 4 p39 6 (0,true) (by decide) (by rfl) (by decide)
    (query_mono hB (by decide : zipQueryOK 2354 p39 6 (0,true) = true))
  intro mv hv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact fun m hm => lift (by omega : 1003 ≤ B) (BB6.Agent11Raw39LA.all0LA m hm)
  · exact cyc B _ 0 8 true 0 (by decide) (by decide)
  · exact h _ (by decide)
  · exact cyc B _ 0 8 true 0 (by decide) (by decide)
  · exact cyc B _ 0 10 true 0 (by decide) (by decide)
  · exact fun m hm => lift (by omega : 1271 ≤ B) (BB6.Agent11Raw39B0RB.allChild m hm)
  · exact h _ (by decide)
  · exact fun m hm => lift (by omega : 175 ≤ B) (BB6.Agent11Raw39.all1RB m hm)
  · exact cyc B _ 13 1 false 1 (by decide) (by decide)
  · exact fun m hm => lift hB (BB6.Agent11Raw39RC.all0RC m hm)
  · exact cyc B _ 0 12 true 0 (by decide) (by decide)
  · exact fun m hm => lift (by omega : 1882 ≤ B) (BB6.Agent11Raw39B1RC.allChild m hm)
  · exact cyc B _ 10 1 false 0 (by decide) (by decide)
  · exact cyc B _ 0 8 true 0 (by decide) (by decide)
  · exact cyc B _ 10 1 false 0 (by decide) (by decide)
  · exact cyc B _ 0 8 true 0 (by decide) (by decide)
  · exact h _ (by decide)
  · exact fun m hm => lift (by omega : 944 ≤ B) (BB6.Agent11Raw39B0RE.allChild m hm)
  · exact h _ (by decide)
  · exact h _ (by decide)
  all_goals exact False.elim ((by decide : ¬ (5 : Nat) ≤ 4) hv)

theorem parent_cover_five (B : Nat) (hB : 2354 ≤ B)
    (h : ∀ mv ∈ remaining, Bound B (child mv)) : Cover (WeightedBound B) p39 :=
  .leaf p39 (parent_bound_five B hB h)

#print axioms remaining_count
#print axioms parent_bound_five
#print axioms parent_cover_five
end BB6.Agent11Raw39AcceptedSix
