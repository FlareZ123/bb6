import OddOddVal3Orbit
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- The full valuation-three odd/odd target cone whose canonical predecessor
    belongs to the previously proved high odd-right forbidden mod-four cone. -/
theorem oddodd_val3_forbidden_parent (x y time : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y)
    (ha : ((x+y-4)/2)%4=2)
    (hk : ((x+3*y-10)/4)%4=3)
    (hkbig : 7≤((x+3*y-10)/4)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro hr
  obtain ⟨n,hn⟩ := (oddodd_val3_blank_reach_iff x y hx hy hy5 hs hsize).mp ⟨time,hr⟩
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have haeq : a=4*(a/4)+2 := by dsimp [a] at ha ⊢; omega
  have hkeq : k=4*((k-7)/4+1)+3 := by dsimp [k] at hk hkbig ⊢; omega
  have hn' : BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k) := hn
  rw [haeq,hkeq] at hn'
  exact blank_no_two_three_high n (a/4) ((k-7)/4) hn'

/-- Infinite high halting family eliminated through the full original-source
    odd/odd valuation-three inverse, rather than finite quotient absence. -/
theorem high_halt_oddodd_val3_unreachable (j m k time : Nat)
    (hm4 : m%4=3)
    (hjm : (j+13*m)%16=10)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  have hm : 3≤m := by omega
  let P : Nat := 2^(2*m+2)
  have h16 : 16∣P := by
    dsimp [P]
    change 2^4∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨d,hd⟩ := h16
  have hmod : (k+j+3*m+5)%16=0 := by
    have hdiv : 16∣k+j+3*m+5 := by
      refine ⟨d*(j+3),?_⟩
      calc
        k+j+3*m+5 = P*(j+3) := hgate
        _ = (16*d)*(j+3) := by rw [hd]
        _ = 16*(d*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hpow : 16*(m+1)≤P := by
    have hh := halting_power_linear (m-2)
    have he : 2*(m-2)+6=2*m+2 := by omega
    have hr : 16*((m-2)+3)=16*(m+1) := by omega
    dsimp [P]
    simpa only [he,hr] using hh
  have hPone : 1≤P := by omega
  have hPj : j≤P*j := by simpa using Nat.mul_le_mul_right j hPone
  have hP3 : 3*m+55≤3*P := by omega
  have hprod : P*(j+3)=P*j+3*P := by rw [Nat.mul_add]; omega
  have hklarge : 50≤k := by
    change k+j+3*m+5=P*(j+3) at hgate
    rw [hprod] at hgate
    omega
  have hx : (2*j+3)%2=1 := by omega
  have hy : k%2=1 := by omega
  have hv : ((2*j+3)+k)%16=8 := by omega
  have hparA : ((((2*j+3)+k-4)/2)%4)=2 := by omega
  have hparK : ((((2*j+3)+3*k-10)/4)%4)=3 := by omega
  have hparLarge : 7≤(((2*j+3)+3*k-10)/4) := by omega
  exact oddodd_val3_forbidden_parent (2*j+3) k time hx hy
    (by omega) hv (by omega) hparA hparK hparLarge

#print axioms oddodd_val3_forbidden_parent
#print axioms high_halt_oddodd_val3_unreachable
end BB6.Agent3
