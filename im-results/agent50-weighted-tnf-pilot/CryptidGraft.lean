import CryptidSiblings
import CryptidsWeightedLeaves

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50CryptidGraft
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent50CryptidSiblings BB6.Agent47WeightedHalt
open BB6.Agent47WeightedHalt.Cryptids BB6.Cryptids608

/-- Pointwise equality of finite partial tables, checked on all twelve slots. -/
def tableEq (a b : PartialMachine) : Bool :=
  (List.finRange 6).all fun q =>
    [false,true].all fun x => decide (a (q,x) = b (q,x))

theorem tableEq_sound (a b : PartialMachine) (h : tableEq a b = true) :
    a = b := by
  funext slot
  rcases slot with ⟨q,x⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hx : x ∈ [false,true] := by cases x <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq x hx)

theorem r2_special_exact : r2.child r2.special = forgetHaltRows expectedRLE_r2 :=
  tableEq_sound _ _ (by decide)

theorem r3_special_exact : r3.child r3.special = forgetHaltRows expectedRLE_r3 :=
  tableEq_sound _ _ (by decide)

theorem r5_special_exact : r5.child r5.special = forgetHaltRows expectedRLE_r5 :=
  tableEq_sound _ _ (by decide)

theorem r6_special_exact : r6.child r6.special = forgetHaltRows expectedRLE_r6 :=
  tableEq_sound _ _ (by decide)

/-- Full expanded parents. The designated child is supplied by the pinned
    upstream nonhalting theorem, never by a simulation cutoff. -/
def r2_certificate : WeightedTNFCertificate r2.bound r2.parent 6 :=
  assemble r2 r2_valid (by rw [r2_special_exact]; exact r2_weighted_leaf r2.bound)

def r3_certificate : WeightedTNFCertificate r3.bound r3.parent 6 :=
  assemble r3 r3_valid (by rw [r3_special_exact]; exact r3_weighted_leaf r3.bound)

def r5_certificate : WeightedTNFCertificate r5.bound r5.parent 6 :=
  assemble r5 r5_valid (by rw [r5_special_exact]; exact r5_weighted_leaf r5.bound)

def r6_certificate : WeightedTNFCertificate r6.bound r6.parent 6 :=
  assemble r6 r6_valid (by rw [r6_special_exact]; exact r6_weighted_leaf r6.bound)

theorem r2_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r2.parent m → WeightedBound B m) ↔ 471 ≤ B :=
  exact_from_attained r2 r2_valid r2_certificate 470 rfl r2_attained B

theorem r3_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r3.parent m → WeightedBound B m) ↔ 1768 ≤ B :=
  exact_from_attained r3 r3_valid r3_certificate 1767 rfl r3_attained B

theorem r5_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r5.parent m → WeightedBound B m) ↔ 28 ≤ B :=
  exact_from_attained r5 r5_valid r5_certificate 27 rfl r5_attained B

theorem r6_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r6.parent m → WeightedBound B m) ↔ 582 ≤ B :=
  exact_from_attained r6 r6_valid r6_certificate 581 rfl r6_attained B

#print axioms r5_special_exact
#print axioms r5_certificate
#print axioms r5_exact_weighted_threshold
#print axioms r3_special_exact
#print axioms r3_certificate
#print axioms r3_exact_weighted_threshold
#print axioms r2_special_exact
#print axioms r6_special_exact
#print axioms r2_certificate
#print axioms r6_certificate
#print axioms r2_exact_weighted_threshold
#print axioms r6_exact_weighted_threshold
end BB6.Agent50CryptidGraft
