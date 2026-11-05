import Lean.Elab.Tactic.Omega
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace NeedleTenParentWitness

def Y : Nat := 479268809023655509957346
def den (v : Nat) : Nat := 2^(v+1)+3
def bias (v : Nat) : Nat := 3*2^v+v+3

def pairs : List (Nat × Nat) :=
  [(0,95853761804731101991468),
   (1,68466972717665072851048),
   (2,43569891729423228177939),
   (3,25224674159139763681964),
   (5,7153265806323216566526),
   (6,3658540526898133663795),
   (9,466668752700735647474),
   (11,116923349359271898012),
   (14,14624784383255180187),
   (15,7312726911055333616)]

def source (p : Nat × Nat) : Nat := 2^p.1*(2*p.2+3)-2

theorem count : pairs.length=10 := by decide
theorem every_affine_parent :
    ∀ p ∈ pairs, den p.1*p.2+bias p.1=Y := by decide
theorem distinct_sources : (pairs.map source).Nodup := by decide

#eval pairs.map source
#print axioms count
#print axioms every_affine_parent
#print axioms distinct_sources
end NeedleTenParentWitness
