import CostMarkerDuality
namespace BB6.Agent50Cost

theorem even_endpoint_sum (p n H Hc X Xc q z w t : Nat)
    (hp : p=2*n) (hp0 : 0<p)
    (hH : H+Hc+1=3*p)
    (hX : X+Xc+3=t*n)
    (ht : t%2=0)
    (hz : p*z=(3+8*H)*q+1+X)
    (hw : p*w=(5+8*Hc)*q+2+Xc) :
    z+w=24*q+t/2 := by
  have hcoef : (3+8*H)+(5+8*Hc)=24*p := by omega
  have he : t=2*(t/2) := by omega
  have hmul : t*n = p*(t/2) := by
    calc
      t*n=(2*(t/2))*n := by rw [←he]
      _ = (2*n)*(t/2) := by ac_rfl
      _ = p*(t/2) := by rw [hp]
  have hall : p*(z+w)=p*(24*q+t/2) := by
    calc
      p*(z+w) = ((3+8*H)+(5+8*Hc))*q+(X+Xc+3) := by
        rw [Nat.mul_add, hz, hw]
        simp only [Nat.add_mul]
        omega
      _ = 24*p*q+t*n := by rw [hcoef,hX]
      _ = p*(24*q+t/2) := by
        rw [hmul, Nat.mul_add]
        ac_rfl
  exact Nat.mul_left_cancel hp0 hall

theorem even_word_endpoint_reflection (bs : List Bool) (q z w : Nat)
    (hh : 1 ≤ bs.length) (heven : bs.length%2=0)
    (hz : 2^bs.length*z=(3+8*marker bs)*q+1+markerScore bs)
    (hw : 2^bs.length*w=(5+8*marker (bs.map (!·)))*q+2+markerScore (bs.map (!·))) :
    2*(z+w)+8=3*(16*q+bs.length+10) := by
  have hp0 : 0<2^bs.length := Nat.pow_pos (by decide)
  have hsum := even_endpoint_sum (2^bs.length) (2^(bs.length-1))
    (marker bs) (marker (bs.map (!·)))
    (markerScore bs) (markerScore (bs.map (!·))) q z w (3*bs.length+22)
    (by
      cases hv: bs.length with
      | zero => omega
      | succ k => simp [hv, Nat.pow_succ, Nat.mul_comm])
    hp0
    (marker_complement bs)
    (markerScore_complement bs hh)
    (by omega) hz hw
  omega

#print axioms even_endpoint_sum
#print axioms even_word_endpoint_reflection
end BB6.Agent50Cost
