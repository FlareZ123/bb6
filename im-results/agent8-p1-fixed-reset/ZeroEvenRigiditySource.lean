import ZeroEvenRigidity
import InverseIff
import PosEvenForm

namespace BB6.Agent8Zero
open BB6.Agent1Quarter BB6.Agent47P1

/-- Source-defined inverseAt with c=0, followed by an original
blank-reachable even-left positive-even target, forces a unique
all-natural dyadic depth j+2 and explicit odd-hub coordinates.
No critical root and no bound on inverse history length are assumed. -/
theorem source_zero_even_rigidity
    (b d t k : Nat) (hb : 8≤b) (hb4 : b%4=0)
    (hdodd : d%2=1)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    ∃ j : Nat, t=j+2 ∧ b=4*(2^j+j) ∧
      d+2*j+3=10*2^j := by
  obtain ⟨hpower,hlinear⟩ :=
    (inverseAt_iff_power_mass b d t k 0 (by omega) hb4 hdodd).mp hinv
  have hpower' : d+b/2+3=3*2^t := by omega
  have hlinear' : 2*k+2*t+1=b+d := by omega
  have hleft : (2*k-4)%2=0 := by omega
  obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape
    (2*k-4) 4 hreach hleft (by decide) (by decide)
  have hreach' : 2*k+8=14*2^j := by omega
  obtain ⟨ht,hb',hd'⟩ := zero_even_numeric_rigidity b d t k j
    hb hb4 (by omega) hpower' hlinear' hreach'
  exact ⟨j,ht,hb',hd'⟩

#print axioms BB6.Agent8Zero.source_zero_even_rigidity
end BB6.Agent8Zero
