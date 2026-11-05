import Lean
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent8Density
/-- Proven P1 n=16q+2 critical-target exclusions, restricted to a
    convenient common modulus 1024 of the q parameter. -/
def q256 : List Nat :=
  [14,30,57,61,73,77,106,138,173,217,218,221,233,238,250,254]

def certified (q : Nat) : Bool :=
  q % 4 == 0 || q % 4 == 3 ||
  q256.contains (q % 256) ||
  q % 1024 == 29 || q % 1024 == 297

def acceptedResidues : List Nat :=
  (List.range 1024).filter certified

/-- The finite exact residue count. Source-valid P1 reachability
    corollaries rely on the separately proved original Reach theorems. -/
theorem certified_density_count : acceptedResidues.length = 578 := by decide

#print axioms certified_density_count
end BB6.Agent8Density
