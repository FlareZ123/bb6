import CFeederCertificate
namespace BB6Agent6.C

private def S1 : List (Nat × Nat × Nat) :=
  [(0,2,14), (1,1,15), (2,0,16), (3,4,3), (3,6,1), (3,7,0), (4,3,4),
    (5,2,5), (6,1,6), (7,0,7)]

private theorem rank1 : rankCheck 18 S1 = true := by decide
private theorem closed1 : boundedCheck 18 S1 = true := by decide
private theorem initial1 : (5,0,1) ∉ S1 := by decide
private theorem mem1 : (0,2,14) ∈ S1 := by decide

/-- Exclude feeder index j=1 from the genuine blank orbit by finite
    backward-closed reachable-set certificate. -/
theorem blank_ne_feeder_1 (n : Nat) :
    run n (5,0,1) ≠ some (0,2,14) :=
  blank_excluded_by_certificate 18 S1 closed1 rank1 initial1
    n (0,2,14) mem1

#print axioms BB6Agent6.C.blank_ne_feeder_1
end BB6Agent6.C
