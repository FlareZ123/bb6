import GInverse
import ShadowDepthArithmetic
import NoC1Arithmetic

namespace BB6.Agent45Exception
open BB6.Agent1
open BB6.P1Reduction
open BB6.Shadow

/-- An authentic positive G output from the special input 1 is impossible
at a dyadically encoded hub whose offset is tiny compared with its scale. -/
theorem encoded_no_special_G_one
    (N L m b d w z alpha k : Nat)
    (hm : m+4≤N)
    (hw : 4≤w) (hz : 0<z)
    (hbeven : b%2=0) (hbpos : 0<b)
    (hmass : b+d+2*m+2*L+3=56*2^N)
    (hoff : L+m=w+z)
    (hcoord : b+4*w=alpha*2^(N-m))
    (hmargin : 2*(L+m)<2^(N-m-2))
    (hG : G k 1=(b,d)) : False := by
  have hsub : (N-m-2)+1=N-m-1 := by omega
  have hpowstep : 2^(N-m-1)=2*2^(N-m-2) := by
    calc
      2^(N-m-1) = 2^((N-m-2)+1) := by rw [hsub]
      _ = 2^(N-m-2)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(N-m-2) := by omega
  have hsmallz : 2*z<2^(N-m-2) := by omega
  have hsmallw : 4*w≤2^(N-m-1) := by omega
  have hsafe : m+(N-m-4)+3≤N := by omega
  have hdiv := encoded_shift_divisible N L m (N-m-4) b d w z alpha
    hmass hoff hcoord hbeven hsafe
  have he : (N-m-4)+2=N-m-2 := by omega
  rw [he] at hdiv
  obtain ⟨t,ht⟩ := G_input_power k 1 b d hG hbpos
  have hpure : d+b/2+3=2^(t+2) := by
    simpa [Nat.pow_add] using ht
  exact encoded_no_pure_power N m b d w z alpha (t+2) hm hw hz
    hbeven hcoord hsmallw hsmallz hdiv hpure

#print axioms encoded_no_special_G_one
end BB6.Agent45Exception
