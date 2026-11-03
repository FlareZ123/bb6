import OddOddOrbit
import OddSevenSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A full 2D source-exact blank-forbidden large even/odd return wedge.
    Its sole predecessor is odd/odd with forbidden sum 2 (mod 4). -/
theorem odd_seven_four_three_unreachable (a k time : Nat)
    (ha : a%8=4) (hk : k%8=3) (hk5 : 5≤k)
    (hs : (a+k+1)%16=8) (hsize : 23≤a+k) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (a,k) := by
  intro h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨b,c⟩
          have hed : secNext (b,c)=some (a,k) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨heq1,heq2⟩ := odd_seven_parent_equations b c a k
            (by omega) (by omega) hk5 hs hsize hed
          have hcodd : c%2=1 := by omega
          have hc5 : 5≤c := by omega
          have hsum : (b+c)%4=2 := by omega
          cases n with
          | zero =>
              simp [BB6.Agent8Section.run] at hp
              omega
          | succ n =>
              have hi := blank_section_odd_image n b c hp hc5 hcodd
              omega

/-- Any odd-odd target with valuation-two total mass and whose canonical
    parent lies in the complete second even/odd forbidden wedge is itself
    forever absent from the true blank section, without a depth cutoff. -/
theorem oddodd_second_wedge_unreachable (x y time : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hv2 : (x+y)%8=4)
    (ha : ((x+y-4)/2)%8=4)
    (hk : ((x+3*y-10)/4)%8=3)
    (hs : (((x+y-4)/2)+((x+3*y-10)/4)+1)%16=8)
    (hsize : 23≤(x+y-4)/2+(x+3*y-10)/4) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro h
  obtain ⟨n,hn⟩ := (oddodd_blank_reach_iff x y hx hy hy5 hv2).mp ⟨time,h⟩
  exact odd_seven_four_three_unreachable _ _ n ha hk (by omega) hs hsize hn

/-- Uniform superlinear lower bound for all high stopping target heights. -/
private theorem high_halt_height (j m k : Nat)
    (hm : 4≤m) (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    200≤k := by
  let P := 2^(2*m+2)
  have hpow : 16*(m+1)≤P := by
    have hh := halting_power_linear (m-2)
    have h1 : 2*(m-2)+6=2*m+2 := by omega
    have h2 : 16*((m-2)+3)=16*(m+1) := by omega
    dsimp [P]
    simpa only [h1,h2] using hh
  have hprod : P*(j+3)=P*j+3*P := by
    rw [Nat.mul_add]
    omega
  have hP1 : 1≤P := by omega
  have hPj : j≤P*j := by simpa using Nat.mul_le_mul_right j hP1
  have hPlarge : 3*m+205≤3*P := by omega
  change k+j+3*m+5=P*(j+3) at hgate
  rw [hprod] at hgate
  omega

/-- A new infinite genuine high-stopping family missed by the previous
    two exact inverse residue wedges. -/
theorem high_halt_oddodd_second_64_unreachable
    (j m k time : Nat)
    (hm : 4≤m) (hm4 : m%4=0)
    (hjm : (j+49*m)%64=62)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  let P : Nat := 2^(2*m+2)
  have hPDiv : 64 ∣ P := by
    dsimp [P]
    change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨d,hd⟩ := hPDiv
  have hmod : (k+j+3*m+5)%64=0 := by
    have hdiv : 64 ∣ k+j+3*m+5 := by
      refine ⟨d*(j+3),?_⟩
      calc
        k+j+3*m+5 = P*(j+3) := hgate
        _ = (64*d)*(j+3) := by rw [hd]
        _ = 64*(d*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hklarge : 200≤k := high_halt_height j m k hm hgate
  have hxodd : (2*j+3)%2=1 := by omega
  have hkodd : k%2=1 := by omega
  have hv2 : ((2*j+3)+k)%8=4 := by omega
  have hpar1 : ((((2*j+3)+k-4)/2)%8)=4 := by omega
  have hpar2 : ((((2*j+3)+3*k-10)/4)%8)=3 := by omega
  have hpar3 :
      (((((2*j+3)+k-4)/2)+(((2*j+3)+3*k-10)/4)+1)%16)=8 := by omega
  have hsize :
      23≤(((2*j+3)+k-4)/2)+(((2*j+3)+3*k-10)/4) := by omega
  exact oddodd_second_wedge_unreachable (2*j+3) k time
    hxodd hkodd (by omega) hv2 hpar1 hpar2 hpar3 hsize

#print axioms odd_seven_four_three_unreachable
#print axioms oddodd_second_wedge_unreachable
#print axioms high_halt_oddodd_second_64_unreachable
end BB6.Agent3
