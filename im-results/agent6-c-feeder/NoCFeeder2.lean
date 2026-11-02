import CFeederCertificate
namespace BB6Agent6.C

private def S2 : List (Nat × Nat × Nat) :=
  [(0,0,3), (0,0,4), (0,0,16), (0,0,23), (0,1,7), (0,2,1), (0,3,0),
    (0,4,11), (0,4,18), (1,0,1), (1,0,8), (1,1,0), (1,3,12), (1,3,19),
    (1,4,3), (1,6,1), (1,7,0), (2,0,3), (2,2,1), (2,2,13), (2,2,20),
    (2,3,0), (2,3,4), (3,1,14), (3,1,21), (3,2,5), (4,0,15), (4,0,22),
    (4,1,6), (5,0,7), (5,7,3), (5,9,1), (5,10,0), (6,6,4), (7,5,5),
    (8,4,6), (9,3,7), (10,2,8), (11,1,9), (12,0,10), (13,1,3), (13,3,1),
    (13,4,0), (14,0,4), (15,0,1), (15,1,0)]

private theorem rank2 : rankCheck 26 S2 = true := by decide
private theorem closed2 : boundedCheck 26 S2 = true := by decide
private theorem initial2 : (5,0,1) ∉ S2 := by decide
private theorem mem2 : (0,4,18) ∈ S2 := by decide

/-- Exclude feeder index j=2 from the genuine blank orbit by finite
    backward-closed reachable-set certificate. -/
theorem blank_ne_feeder_2 (n : Nat) :
    run n (5,0,1) ≠ some (0,4,18) :=
  blank_excluded_by_certificate 26 S2 closed2 rank2 initial2
    n (0,4,18) mem2

#print axioms BB6Agent6.C.blank_ne_feeder_2
end BB6Agent6.C
