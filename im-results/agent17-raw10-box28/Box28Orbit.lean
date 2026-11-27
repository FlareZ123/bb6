import Box28Symmetry
import Box28Simple

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17.Box28Orbit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot)
open BB6.Agent17.Box28Symmetry

abbrev sourceDomain := sourceCut
def eCode (d : Fin 4) : Fin 25 := ⟨17+d.val,by omega⟩
def fCode (d : Fin 4) : Fin 25 := ⟨21+d.val,by omega⟩
theorem ef_f_to_e : ∀ d : Fin 4, efCode (fCode d) = eCode d := by decide

theorem ef_bound (B : Nat) (d : Fin 4)
    (h : ∀ m, Fits (sourceDomain (eCode d)) m → WeightedBound B m)
    (m : Machine) (hm : Fits (sourceDomain (fCode d)) m) : WeightedBound B m := by
  apply transportFor 14 (fCode d) (B := B) ?_ m hm
  intro m' hm'
  rw [show efCode 14 = 14 by decide, ef_f_to_e] at hm'
  exact h m' hm'

theorem decode_surjective (t : Transition) : ∃ v : Fin 25, decode v = t := by
  cases t with
  | none => exact ⟨0,rfl⟩
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    revert q r w
    decide

def hardCodes : List (Fin 25) := [3,4,17,18,19,20]
def hardCodes16 : List (Fin 25) := [1,3,4,5,7,8,17,18,19,20]

theorem classify : ∀ d1 : Fin 25,
    (BB6.Agent17.Box28Simple.secondWitness 14 d1).isSome = true ∨
    d1 ∈ hardCodes ∨ ∃ d : Fin 4, d1 = fCode d := by decide

theorem classify16 : ∀ d1 : Fin 25,
    (BB6.Agent17.Box28Simple.secondWitness 16 d1).isSome = true ∨
    d1 ∈ hardCodes16 ∨ ∃ d : Fin 4, d1 = fCode d := by decide

theorem fixedD0_bound (B : Nat) (hB : 11 ≤ B) (d0 : Fin 25)
    (hfix : efCode d0 = d0) (hard : List (Fin 25))
    (hclass : ∀ d1 : Fin 25,
      (BB6.Agent17.Box28Simple.secondWitness d0 d1).isSome = true ∨
      d1 ∈ hard ∨ ∃ d : Fin 4, d1 = fCode d)
    (hmem : ∀ d : Fin 4, eCode d ∈ hard)
    (h : ∀ d1 ∈ hard, ∀ m, Fits (sourceCutFor d0 d1) m → WeightedBound B m)
    (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (3,false) = decode d0) : WeightedBound B m := by
  obtain ⟨d1,he⟩ := decode_surjective (m (3,true))
  have hf := sourceCutFor_fits d0 d1 m hm h0 he.symm
  rcases hclass d1 with hs | hh | ⟨d,hd⟩
  · have hb := BB6.Agent17.Box28Simple.parent_second m hm d0 d1 h0 he.symm hs
    intro k j hk hj
    exact Nat.le_trans (hb k j hk hj) hB
  · exact h d1 hh m hf
  · subst d1
    apply transportFor d0 (fCode d) (B := B) ?_ m hf
    intro m' hm'
    rw [hfix,ef_f_to_e] at hm'
    exact h (eCode d) (hmem d) m' hm'

theorem d14_bound (B : Nat) (hB : 11 ≤ B)
    (h : ∀ d1 ∈ hardCodes, ∀ m, Fits (sourceDomain d1) m → WeightedBound B m)
    (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (3,false) = decode 14) : WeightedBound B m :=
  fixedD0_bound B hB 14 (by decide) hardCodes classify (by decide) h m hm h0

theorem d16_bound (B : Nat) (hB : 11 ≤ B)
    (h : ∀ d1 ∈ hardCodes16, ∀ m, Fits (sourceCutFor 16 d1) m → WeightedBound B m)
    (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (3,false) = decode 16) : WeightedBound B m :=
  fixedD0_bound B hB 16 (by decide) hardCodes16 classify16 (by decide) h m hm h0

#print axioms ef_bound
#print axioms d14_bound
#print axioms d16_bound
end BB6.Agent17.Box28Orbit
