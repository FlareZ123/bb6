import FirstHolePath
import Nov26Pair1
import Nov26Pair2
import Nov26Pair3
import Nov26Pair4
import Nov26Pair5
import Nov26Pair6
import Nov26Pair7
import Nov26Pair8
import Nov26Pair9

namespace BB6.Agent10Nov26
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf_eq_forget (m : Machine) : leaf m = forgetHaltRows m := rfl

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n1_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (4, (4, true)), (5, (1, true)), (6, (5, false)), (7, (4, false)), (11, (3, true)), (12, (0, true)), (24, (5, true))]
theorem n1_reachable : FirstHolePath (leaf n1) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n1 n1_path (by decide +kernel)
def n1_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n1) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n1 (by rfl) n1_never
theorem n1_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n1) :=
  (n1_weighted_cert B).toCover
#print axioms n1_reachable
#print axioms n1_weighted_cover

/-- Raw9: actual first-hole schedule, with arbitrary score bound. -/
def n2_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (4, (1, true)), (5, (3, false)), (6, (4, true)), (7, (0, true)), (8, (3, true)), (9, (4, false)), (10, (5, false)), (13, (2, true))]
theorem n2_reachable : FirstHolePath (leaf n2) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n2 n2_path (by decide +kernel)
def n2_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n2) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n2 (by rfl) n2_never
theorem n2_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n2) :=
  (n2_weighted_cert B).toCover
#print axioms n2_reachable
#print axioms n2_weighted_cover

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n3_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (2, false)), (5, (1, true)), (6, (3, false)), (7, (4, true)), (8, (5, false)), (9, (3, true)), (12, (4, false)), (28, (0, true))]
theorem n3_reachable : FirstHolePath (leaf n3) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n3 n3_path (by decide +kernel)
def n3_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n3) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n3 (by rfl) n3_never
theorem n3_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n3) :=
  (n3_weighted_cert B).toCover
#print axioms n3_reachable
#print axioms n3_weighted_cover

/-- Raw140: actual first-hole schedule, with arbitrary score bound. -/
def n4_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (0, true)), (5, (4, true)), (6, (5, true)), (9, (1, true)), (16, (5, false)), (18, (2, true)), (21, (3, true))]
theorem n4_reachable : FirstHolePath (leaf n4) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n4 n4_path (by decide +kernel)
def n4_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n4) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n4 (by rfl) n4_never
theorem n4_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n4) :=
  (n4_weighted_cert B).toCover
#print axioms n4_reachable
#print axioms n4_weighted_cover

/-- Raw140: actual first-hole schedule, with arbitrary score bound. -/
def n5_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (0, true)), (5, (4, true)), (7, (4, false)), (13, (3, true)), (14, (5, false)), (23, (5, true)), (85, (2, true))]
theorem n5_reachable : FirstHolePath (leaf n5) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n5 n5_path (by decide +kernel)
def n5_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n5) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n5 (by rfl) n5_never
theorem n5_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n5) :=
  (n5_weighted_cert B).toCover
#print axioms n5_reachable
#print axioms n5_weighted_cover

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n6_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, true)), (4, (4, false)), (5, (0, true)), (6, (5, false)), (8, (2, false)), (10, (5, true)), (16, (4, true)), (25, (1, true))]
theorem n6_reachable : FirstHolePath (leaf n6) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n6 n6_path (by decide +kernel)
def n6_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n6) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n6 (by rfl) n6_never
theorem n6_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n6) :=
  (n6_weighted_cert B).toCover
#print axioms n6_reachable
#print axioms n6_weighted_cover

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n7_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (4, (2, false)), (5, (3, true)), (6, (4, true)), (8, (4, false)), (14, (1, true)), (17, (0, true)), (18, (5, false)), (20, (5, true))]
theorem n7_reachable : FirstHolePath (leaf n7) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n7 n7_path (by decide +kernel)
def n7_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n7) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n7 (by rfl) n7_never
theorem n7_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n7) :=
  (n7_weighted_cert B).toCover
#print axioms n7_reachable
#print axioms n7_weighted_cover

/-- Raw140: actual first-hole schedule, with arbitrary score bound. -/
def n8_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (4, true)), (5, (5, true)), (6, (2, true)), (10, (5, false)), (11, (1, true)), (12, (3, true)), (39, (0, true))]
theorem n8_reachable : FirstHolePath (leaf n8) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n8 n8_path (by decide +kernel)
def n8_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n8) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n8 (by rfl) n8_never
theorem n8_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n8) :=
  (n8_weighted_cert B).toCover
#print axioms n8_reachable
#print axioms n8_weighted_cover

/-- Raw139: actual first-hole schedule, with arbitrary score bound. -/
def n9_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, true)), (5, (3, false)), (6, (4, false)), (7, (0, true)), (10, (4, true)), (11, (5, false)), (16, (2, true)), (18, (5, true))]
theorem n9_reachable : FirstHolePath (leaf n9) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n9 n9_path (by decide +kernel)
def n9_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n9) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n9 (by rfl) n9_never
theorem n9_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n9) :=
  (n9_weighted_cert B).toCover
#print axioms n9_reachable
#print axioms n9_weighted_cover

/-- Raw13: actual first-hole schedule, with arbitrary score bound. -/
def n10_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (0, true)), (4, (3, true)), (5, (4, false)), (6, (1, true)), (7, (5, false)), (8, (2, true)), (19, (5, true)), (25, (4, true))]
theorem n10_reachable : FirstHolePath (leaf n10) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n10 n10_path (by decide +kernel)
def n10_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n10) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n10 (by rfl) n10_never
theorem n10_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n10) :=
  (n10_weighted_cert B).toCover
#print axioms n10_reachable
#print axioms n10_weighted_cover

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n11_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, true)), (4, (4, false)), (6, (2, false)), (7, (5, true)), (11, (5, false)), (12, (4, true)), (26, (1, true)), (29, (0, true))]
theorem n11_reachable : FirstHolePath (leaf n11) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n11 n11_path (by decide +kernel)
def n11_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n11) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n11 (by rfl) n11_never
theorem n11_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n11) :=
  (n11_weighted_cert B).toCover
#print axioms n11_reachable
#print axioms n11_weighted_cover

/-- Raw140: actual first-hole schedule, with arbitrary score bound. -/
def n12_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (1, true)), (5, (3, true)), (6, (4, true)), (8, (4, false)), (24, (2, true)), (5987, (0, true)), (5988, (5, false))]
theorem n12_reachable : FirstHolePath (leaf n12) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n12 n12_path (by decide +kernel)
def n12_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n12) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n12 (by rfl) n12_never
theorem n12_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n12) :=
  (n12_weighted_cert B).toCover
#print axioms n12_reachable
#print axioms n12_weighted_cover

/-- Raw9: actual first-hole schedule, with arbitrary score bound. -/
def n13_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (4, true)), (5, (0, true)), (6, (2, true)), (35, (4, false)), (36, (5, false)), (38, (1, true)), (120, (5, true))]
theorem n13_reachable : FirstHolePath (leaf n13) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n13 n13_path (by decide +kernel)
def n13_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n13) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n13 (by rfl) n13_never
theorem n13_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n13) :=
  (n13_weighted_cert B).toCover
#print axioms n13_reachable
#print axioms n13_weighted_cover

/-- Raw139: actual first-hole schedule, with arbitrary score bound. -/
def n14_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, true)), (4, (4, true)), (7, (2, true)), (12, (0, true)), (21, (4, false)), (22, (5, false)), (24, (3, false)), (26, (1, true))]
theorem n14_reachable : FirstHolePath (leaf n14) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n14 n14_path (by decide +kernel)
def n14_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n14) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n14 (by rfl) n14_never
theorem n14_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n14) :=
  (n14_weighted_cert B).toCover
#print axioms n14_reachable
#print axioms n14_weighted_cover

/-- Raw9: actual first-hole schedule, with arbitrary score bound. -/
def n15_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (4, true)), (7, (4, false)), (10, (2, true)), (13, (1, true)), (18, (0, true)), (19, (5, false)), (30, (3, true))]
theorem n15_reachable : FirstHolePath (leaf n15) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n15 n15_path (by decide +kernel)
def n15_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n15) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n15 (by rfl) n15_never
theorem n15_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n15) :=
  (n15_weighted_cert B).toCover
#print axioms n15_reachable
#print axioms n15_weighted_cover

/-- Raw140: actual first-hole schedule, with arbitrary score bound. -/
def n16_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (4, (4, true)), (5, (3, true)), (6, (5, true)), (8, (1, true)), (10, (2, true)), (16, (5, false)), (28, (0, true))]
theorem n16_reachable : FirstHolePath (leaf n16) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n16 n16_path (by decide +kernel)
def n16_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n16) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n16 (by rfl) n16_never
theorem n16_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n16) :=
  (n16_weighted_cert B).toCover
#print axioms n16_reachable
#print axioms n16_weighted_cover

/-- Raw8: actual first-hole schedule, with arbitrary score bound. -/
def n17_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (5, (2, false)), (7, (1, true)), (8, (4, false)), (9, (5, false)), (16, (3, true)), (27, (0, true)), (63, (5, true))]
theorem n17_reachable : FirstHolePath (leaf n17) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n17 n17_path (by decide +kernel)
def n17_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n17) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n17 (by rfl) n17_never
theorem n17_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n17) :=
  (n17_weighted_cert B).toCover
#print axioms n17_reachable
#print axioms n17_weighted_cover

/-- Raw10: actual first-hole schedule, with arbitrary score bound. -/
def n18_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (5, (2, false)), (7, (1, true)), (8, (0, true)), (9, (4, true)), (11, (4, false)), (2053, (3, true)), (2054, (5, false))]
theorem n18_reachable : FirstHolePath (leaf n18) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n18 n18_path (by decide +kernel)
def n18_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n18) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n18 (by rfl) n18_never
theorem n18_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n18) :=
  (n18_weighted_cert B).toCover
#print axioms n18_reachable
#print axioms n18_weighted_cover

end BB6.Agent10Nov26
