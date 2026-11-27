import Raw13Coupled4
import Raw13Coupled5SiblingZeroLA
import Raw13Coupled5SiblingZeroLB
import Raw13Coupled5SiblingZeroLC
import Raw13Coupled5SiblingZeroLD
import Raw13Coupled5SiblingZeroLE
import Raw13Coupled5SiblingZeroLF
import Raw13Coupled5SiblingZeroRB
import Raw13Coupled5SiblingZeroRC
import Raw13Coupled5SiblingZeroRE
import Raw13Coupled5SiblingZeroRF
import Raw13Coupled5SiblingOneLA
import Raw13Coupled5SiblingOneLB
import Raw13Coupled5SiblingOneLC
import Raw13Coupled5SiblingOneLD
import Raw13Coupled5SiblingOneLE
import Raw13Coupled5SiblingOneRA
import Raw13Coupled5SiblingOneRE
import Raw13Coupled5SiblingOneRF

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled5
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit
open BB6.Agent46Raw13CoupledParent

abbrev parent := p4
def kids (h : NeverHalts published) : Move → Cut := byCutMove [
  .bounded BB6.Raw13Coupled5SiblingZeroLA.parent 1007 BB6.Raw13Coupled5SiblingZeroLA.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroLB.parent 1007 BB6.Raw13Coupled5SiblingZeroLB.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroLC.parent 1007 BB6.Raw13Coupled5SiblingZeroLC.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroLD.parent 1007 BB6.Raw13Coupled5SiblingZeroLD.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroLE.parent 1007 BB6.Raw13Coupled5SiblingZeroLE.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroLF.parent 1007 BB6.Raw13Coupled5SiblingZeroLF.bound,
  .closed (.cycle 0 10 true (-1)),
  .bounded BB6.Raw13Coupled5SiblingZeroRB.parent 1007 BB6.Raw13Coupled5SiblingZeroRB.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroRC.parent 1007 BB6.Raw13Coupled5SiblingZeroRC.bound,
  .closed (.cycle 9 1 true 3),
  .bounded BB6.Raw13Coupled5SiblingZeroRE.parent 1007 BB6.Raw13Coupled5SiblingZeroRE.bound,
  .bounded BB6.Raw13Coupled5SiblingZeroRF.parent 1007 BB6.Raw13Coupled5SiblingZeroRF.bound,
  .bounded BB6.Raw13Coupled5SiblingOneLA.parent 10007 BB6.Raw13Coupled5SiblingOneLA.bound,
  .bounded BB6.Raw13Coupled5SiblingOneLB.parent 10007 BB6.Raw13Coupled5SiblingOneLB.bound,
  .bounded BB6.Raw13Coupled5SiblingOneLC.parent 10007 BB6.Raw13Coupled5SiblingOneLC.bound,
  .bounded BB6.Raw13Coupled5SiblingOneLD.parent 1007 BB6.Raw13Coupled5SiblingOneLD.bound,
  .bounded BB6.Raw13Coupled5SiblingOneLE.parent 1007 BB6.Raw13Coupled5SiblingOneLE.bound,
  .bounded BB6.Agent46Raw13Coupled4.parent 62123 (BB6.Agent46Raw13Coupled4.bound h),
  .bounded BB6.Raw13Coupled5SiblingOneRA.parent 1007 BB6.Raw13Coupled5SiblingOneRA.bound,
  .closed (.cycle 1 9 true (-1)),
  .closed (.cycle 7 6 true 1),
  .closed (.cycle 9 1 true 3),
  .bounded BB6.Raw13Coupled5SiblingOneRE.parent 1007 BB6.Raw13Coupled5SiblingOneRE.bound,
  .bounded BB6.Raw13Coupled5SiblingOneRF.parent 10007 BB6.Raw13Coupled5SiblingOneRF.bound]
def parentCut (h : NeverHalts published) : Cut := .split 9 (3,false) (kids h)

theorem parent_support : TNFSupport parent 5 := by
  have h1 : TNFSupport p1 4 := refine_support BB6.Agent46Raw13.raw13 (0,true) ⟨true,false,3⟩ 3 4 BB6.Agent46Raw13.raw13_support (by decide) (by decide) (by decide)
  have h2 : TNFSupport p2 4 := refine_support p1 (3,true) ⟨false,false,0⟩ 4 4 h1 (by decide) (by decide) (by decide)
  have h3 : TNFSupport p3 5 := refine_support p2 (2,true) ⟨true,true,4⟩ 4 5 h2 (by decide) (by decide) (by decide)
  exact refine_support p3 (4,true) ⟨false,true,3⟩ 5 5 h3 (by decide) (by decide) (by decide)
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent46Raw13.raw13_nohalt)))
theorem checked (h : NeverHalts published) : check 62123 parent 5 (parentCut h) = true := by rfl
theorem complete (h : NeverHalts published) : closedCut 5 (parentCut h) = true := by rfl
theorem empty_complement (h : NeverHalts published) : residuals parent 5 (parentCut h) = [] :=
  residuals_empty_of_closedCut (complete h)
theorem bound_quotient (h : NeverHalts published) (m : Machine)
    (hm : TNFQuotientCompatible parent m) : WeightedBound 62123 m := by
  rcases sound 62123 parent 5 (parentCut h) (by decide) parent_support (by decide)
      parent_nohalt (checked h) m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [empty_complement h] at he
    simp at he
theorem bound (h : NeverHalts published) (m : Machine) (hm : compatible parent m) : WeightedBound 62123 m := by
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

abbrev witness := BB6.Agent46Raw13Coupled4.L0.witness
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
theorem exact_threshold (h : NeverHalts published) (N : Nat) :
    (∀ m, compatible parent m → WeightedBound N m) ↔ 62123 ≤ N := by
  constructor
  · intro hb
    have hd : 0 ∈ delays (zeroNext witness) 0 :=
      (mem_delays_iff (by decide)).mpr ⟨0, TerminalPath.stop 0 (by decide)⟩
    have hw := hb _ witness_compatible 62122 0 BB6.Agent46Raw13Coupled4.L0.witness_halts hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (bound h m hm k d hk hd) hb
#print axioms checked
#print axioms empty_complement
#print axioms bound_quotient
#print axioms exact_threshold
end BB6.Agent46Raw13Coupled5
