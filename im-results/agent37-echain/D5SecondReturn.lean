import OddDepthSecondReturn

set_option maxRecDepth 180000
set_option maxHeartbeats 100000000

namespace BB6.Agent37Depth5SecondReturn

open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent31PacketSource
open BB6.Agent37OddDepthSecondReturn

def modulus : Nat := 3^87
def seedS : Nat := 296803664795654310964410044076883765488392

def familyS (v : Nat) : Nat := seedS + modulus*v
def familyH (v : Nat) : Nat := 5 + 54*familyS v
def familyK (v : Nat) : Nat := 607 + 6561*familyS v
def familyT (v : Nat) : Nat := 24272 + 262144*familyS v
def familyR (v : Nat) : Nat := 123233840 + 134217728*v

def d5Packet (v : Nat) : CryptidBoundary.Cfg :=
  packet (3*familyK v+4) 6 2 (false::List.replicate 6 true)

/-- The depth-five reset index has exactly the required 3-adic factor. -/
theorem reset_alignment (v : Nat) :
    2*familyK v+1 = 3^5*familyH v := by
  simp [familyK,familyH,familyS]
  omega

/-- After five E-chain calls the index is in the double-B residue. -/
theorem double_B_alignment (v : Nat) :
    1+4*8^5*familyH v = 27*familyT v+17 := by
  simp [familyH,familyT,familyS]
  omega

/-- Exact 3^87 alignment with the 86-step seed L(24956,2,2). -/
theorem endpoint_alignment (v : Nat) :
    oddEndpoint 2 (familyT v) = 24956 + 3^87*familyR v := by
  simp [oddEndpoint,familyT,familyR,familyS,modulus,seedS]
  omega

/-- A new infinite depth-five prepared P2 cylinder has a second
    source-certified return to a canonical DRegular section.  This is a
    prepared-packet theorem and makes no blank-root reachability claim. -/
theorem d5_family_second_reentry (v : Nat) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (oddResetTime 2 (familyK v) (familyH v) (familyT v) +
            DRegular.accumulated 86
              (oddEndpointState 2 (familyT v)) + T)
          (d5Packet v))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  have hh : 1 ≤ familyH v := by
    unfold familyH
    omega
  have h := odd_depth_aligned_second_reentry
    2 (familyK v) (familyH v) (familyT v) (familyR v)
    hh (reset_alignment v) (double_B_alignment v) (endpoint_alignment v)
  simpa [d5Packet] using h

#print axioms reset_alignment
#print axioms double_B_alignment
#print axioms endpoint_alignment
#print axioms d5_family_second_reentry

end BB6.Agent37Depth5SecondReturn
