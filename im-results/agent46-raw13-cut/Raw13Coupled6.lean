import Raw13Coupled5
import Raw13Coupled6SiblingZeroLA
import Raw13Coupled6SiblingZeroLB
import Raw13Coupled6SiblingZeroLC
import Raw13Coupled6SiblingZeroLD
import Raw13Coupled6SiblingZeroLE
import Raw13Coupled6SiblingZeroLF
import Raw13Coupled6SiblingZeroRB
import Raw13Coupled6SiblingZeroRC
import Raw13Coupled6SiblingZeroRE
import Raw13Coupled6SiblingZeroRF
import Raw13Coupled6SiblingOneLA
import Raw13Coupled6SiblingOneLB
import Raw13Coupled6SiblingOneLD
import Raw13Coupled6SiblingOneLE
import Raw13Coupled6SiblingOneLF
import Raw13Coupled6SiblingOneRA
import Raw13Coupled6SiblingOneRB
import Raw13Coupled6SiblingOneRC
import Raw13Coupled6SiblingOneRD
import Raw13Coupled6SiblingOneRE
import Raw13Coupled6SiblingOneRF

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit
open BB6.Agent46Raw13CoupledParent

def B : Nat := 44423003584937617011264491061
abbrev parent := p3
def kids (h : NeverHalts published) : Move → Cut := byCutMove [
  .bounded BB6.Raw13Coupled6SiblingZeroLA.parent 62123 BB6.Raw13Coupled6SiblingZeroLA.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroLB.parent 62123 BB6.Raw13Coupled6SiblingZeroLB.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroLC.parent 62123 BB6.Raw13Coupled6SiblingZeroLC.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroLD.parent 62123 BB6.Raw13Coupled6SiblingZeroLD.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroLE.parent 62123 BB6.Raw13Coupled6SiblingZeroLE.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroLF.parent 62123 BB6.Raw13Coupled6SiblingZeroLF.bound,
  .closed (.cycle 0 9 true (-1)),
  .bounded BB6.Raw13Coupled6SiblingZeroRB.parent 62123 BB6.Raw13Coupled6SiblingZeroRB.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroRC.parent 62123 BB6.Raw13Coupled6SiblingZeroRC.bound,
  .bounded BB6.Agent46Raw13Coupled5.parent 62123 (BB6.Agent46Raw13Coupled5.bound h),
  .bounded BB6.Raw13Coupled6SiblingZeroRE.parent 62123 BB6.Raw13Coupled6SiblingZeroRE.bound,
  .bounded BB6.Raw13Coupled6SiblingZeroRF.parent 62123 BB6.Raw13Coupled6SiblingZeroRF.bound,
  .bounded BB6.Raw13Coupled6SiblingOneLA.parent 62123 BB6.Raw13Coupled6SiblingOneLA.bound,
  .bounded BB6.Raw13Coupled6SiblingOneLB.parent 2651340 BB6.Raw13Coupled6SiblingOneLB.bound,
  .closed (.cycle 7 2 true 1),
  .bounded BB6.Raw13Coupled6SiblingOneLD.parent 2651346 BB6.Raw13Coupled6SiblingOneLD.bound,
  .bounded BB6.Raw13Coupled6SiblingOneLE.parent 62123 BB6.Raw13Coupled6SiblingOneLE.bound,
  .bounded BB6.Raw13Coupled6SiblingOneLF.parent 62123 BB6.Raw13Coupled6SiblingOneLF.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRA.parent 44423003584937617011264491061 BB6.Raw13Coupled6SiblingOneRA.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRB.parent 62123 BB6.Raw13Coupled6SiblingOneRB.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRC.parent 62123 BB6.Raw13Coupled6SiblingOneRC.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRD.parent 2651346 BB6.Raw13Coupled6SiblingOneRD.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRE.parent 62123 BB6.Raw13Coupled6SiblingOneRE.bound,
  .bounded BB6.Raw13Coupled6SiblingOneRF.parent 62123 BB6.Raw13Coupled6SiblingOneRF.bound]
def parentCut (h : NeverHalts published) : Cut := .split 8 (4,true) (kids h)

theorem parent_support : TNFSupport parent 5 := by
  have h1 : TNFSupport p1 4 := refine_support BB6.Agent46Raw13.raw13 (0,true) ⟨true,false,3⟩ 3 4 BB6.Agent46Raw13.raw13_support (by decide) (by decide) (by decide)
  have h2 : TNFSupport p2 4 := refine_support p1 (3,true) ⟨false,false,0⟩ 4 4 h1 (by decide) (by decide) (by decide)
  exact refine_support p2 (2,true) ⟨true,true,4⟩ 4 5 h2 (by decide) (by decide) (by decide)
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent46Raw13.raw13_nohalt))
theorem checked (h : NeverHalts published) : check B parent 5 (parentCut h) = true := by rfl
theorem complete (h : NeverHalts published) : closedCut 5 (parentCut h) = true := by rfl
theorem empty_complement (h : NeverHalts published) : residuals parent 5 (parentCut h) = [] :=
  residuals_empty_of_closedCut (complete h)
theorem bound_quotient (h : NeverHalts published) (m : Machine)
    (hm : TNFQuotientCompatible parent m) : WeightedBound B m := by
  rcases sound B parent 5 (parentCut h) (by decide) parent_support (by decide)
      parent_nohalt (checked h) m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [empty_complement h] at he
    simp at he
theorem bound (h : NeverHalts published) (m : Machine) (hm : compatible parent m) : WeightedBound B m := by
  let e : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  apply bound_quotient h m
  refine ⟨e,rfl,?_⟩
  have he : renameTable e m = m := by
    funext s
    rcases s with ⟨q,b⟩
    unfold renameTable
    change (m (q,b)).map (renameMove e) = m (q,b)
    cases hh : m (q,b) with
    | none => rfl
    | some mv => cases mv <;> rfl
  rw [he]
  exact hm

abbrev witness := weightedTNFDefaultCompletion BB6Coverage.Agent31Pump.Raw13Coupled6OneRAHierarchy.p
theorem witness_compatible : compatible parent witness := by
  have hpoint : ∀ s : Slot, parent s = none ∨ parent s = some (witness s) := by
    intro s
    rcases s with ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
  intro s t hs
  rcases hpoint s with h | h
  · rw [h] at hs
    contradiction
  · exact Option.some.inj (h.symm.trans hs)
theorem witness_halts : HaltsAfter witness BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay.count :=
  BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay.raw13OneRA_halts
theorem exact_threshold (h : NeverHalts published) (N : Nat) :
    (∀ m, compatible parent m → WeightedBound N m) ↔ B ≤ N := by
  constructor
  · intro hb
    have hz := firstOne_terminal parent (by decide) witness witness_compatible
    have hd : 0 ∈ delays (zeroNext witness) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hw := hb witness witness_compatible BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay.count 0 witness_halts hd
    change 44423003584937617011264491061 ≤ N
    change 44423003584937617011264491060 < N at hw
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (bound h m hm k d hk hd) hb
#print axioms checked
#print axioms empty_complement
#print axioms bound_quotient
#print axioms exact_threshold
end BB6.Agent46Raw13Coupled6
