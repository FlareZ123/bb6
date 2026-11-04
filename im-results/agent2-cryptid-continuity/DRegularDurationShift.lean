import Lean.Elab.Tactic.Omega
import DRegularShift

set_option linter.unusedSimpArgs false

namespace BB6.DRegularDurationShift
open DRegular BB6.DRegularShift

/-- The first derivative of the exact source-model primitive cost with
    respect to an added three-cell unary block. -/
def slope (s : L) : Nat :=
  24 * (if s.a % 3 = 2 then s.a / 3 else s.a / 3 - 1) + 49 +
  (if s.a % 3 = 0 then if s.q = 0 then 0 else 24 * ((s.b+1)/3) else 0)

private theorem quadratic (k p r c : Nat) :
    12*(k+p)*(k+p) + (49+24*r)*(k+p)+c =
      12*k*k + (49+24*r)*k+c + (24*k+49+24*r)*p + 12*p*p := by
  have h : p*k = k*p := Nat.mul_comm p k
  have h2 : p*r=r*p := Nat.mul_comm p r
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

private def acost (k u r d c : Nat) : Nat :=
  (12*k*k+41*k+32) +
  (2*u+r*(6*(4*k+3+u)+41)+12*r*(r-1))+
  2*(4*k+3+d)+c

private theorem acost_shift (k p u r d c : Nat) :
    acost (k+p) u r d c =
      acost k u r d c + (24*k+49+24*r)*p + 12*p*p := by
  simp only [acost, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  have h : p*k=k*p := Nat.mul_comm p k
  have h2 : p*r=r*p := Nat.mul_comm p r
  have h3 : r*p=p*r := Nat.mul_comm r p
  have hextra : r*(6*(4*p)) = 24*r*p := by
    calc
      r*(6*(4*p)) = (6*4)*r*p := by ac_rfl
      _ = 24*r*p := by rfl
  have hextra2 : (24*r)*p = 24*(r*p) := by ac_rfl
  omega

private def aextra (b : Nat) : Nat :=
  if (b+1)%3 = 0 then 6 else if (b+1)%3 = 1 then 10 else 16
private def eextra (q b : Nat) : Nat :=
  if q=0 then 50
  else if b=0 then 50+4*q
  else if b=1 then if q=1 then 96 else 56+4*q
  else 52+6*q

private theorem a_cost_normal (a q b : Nat)
    (h2 : a%3≠2) (h0 : a%3=0) (hq : q≠0) :
    duration ⟨a,q,b⟩ =
      acost (a/3-1) (q-1) ((b+1)/3) ((q-1)+4*((b+1)/3)) (aextra b) := by
  by_cases b0 : (b+1)%3=0
  · simp [duration,acost,aextra,h2,h0,hq,b0,Nat.add_assoc]
  · by_cases b1 : (b+1)%3=1
    · simp [duration,acost,aextra,h2,h0,hq,b0,b1,Nat.add_assoc]
    · simp [duration,acost,aextra,h2,h0,hq,b0,b1,Nat.add_assoc]

private theorem e_cost_normal (a q b : Nat)
    (h2 : a%3≠2) (h0 : a%3≠0) :
    duration ⟨a,q,b⟩ =
      12*(a/3-1)*(a/3-1)+49*(a/3-1)+eextra q b := by
  by_cases q0 : q=0
  · simp [duration,eextra,h2,h0,q0,Nat.add_assoc]
  · by_cases b0 : b=0
    · simp [duration,eextra,h2,h0,q0,b0,Nat.add_assoc]
    · by_cases b1 : b=1
      · by_cases q1 : q=1
        · simp [duration,eextra,h2,h0,q0,b0,b1,q1,Nat.add_assoc]
        · simp [duration,eextra,h2,h0,q0,b1,q1,Nat.add_assoc]
      · simp [duration,eextra,h2,h0,q0,b0,b1,Nat.add_assoc]

/-- For EVERY a≥2 and q,b, the eleven-case D source macro
    has exactly the SAME quadratic 12*p² term when adding 3p
    unary cells. The branch-specific linear term is slope(s)*p. -/
theorem duration_shift (s : L) (hs : 2 ≤ s.a) (p : Nat) :
    duration (bumpInput s p) = duration s + slope s * p + 12*p*p := by
  cases s with
  | mk a q b =>
    change 2 ≤ a at hs
    have hrem : (a + 3*p) % 3 = a % 3 := by omega
    have hdiv : (a + 3*p) / 3 = a/3+p := by omega
    by_cases c2 : a%3=2
    · simpa [duration,bumpInput,slope,hrem,hdiv,c2, Nat.add_assoc] using
        (quadratic (a/3) p 0 40)
    · have hge : 3 ≤ a := by omega
      have hsub : (a+3*p)/3-1 = (a/3-1)+p := by omega
      by_cases c0 : a%3=0
      · by_cases z0 : q=0
        · simpa [duration,bumpInput,slope,hrem,hsub,c2,c0,z0,Nat.add_assoc] using
            (quadratic (a/3-1) p 0 44)
        · have hsource : duration (bumpInput ⟨a,q,b⟩ p) =
              acost (a/3-1+p) (q-1) ((b+1)/3) ((q-1)+4*((b+1)/3)) (aextra b) := by
            simpa only [bumpInput, hsub] using
              (a_cost_normal (a+3*p) q b (by omega) (by omega) z0)
          have htarget := a_cost_normal a q b c2 c0 z0
          rw [hsource,htarget]
          simp [slope,c2,c0,z0,hrem,hdiv]
          exact acost_shift (a/3-1) p (q-1) ((b+1)/3)
            ((q-1)+4*((b+1)/3)) (aextra b)
      · have hsource : duration (bumpInput ⟨a,q,b⟩ p) =
            12*((a/3-1)+p)*((a/3-1)+p)+49*((a/3-1)+p)+eextra q b := by
          simpa only [bumpInput, hsub] using
            (e_cost_normal (a+3*p) q b (by omega) (by omega))
        have htarget := e_cost_normal a q b c2 c0
        rw [hsource,htarget]
        simp [slope,c2,c0]
        simpa [Nat.add_assoc] using (quadratic (a/3-1) p 0 (eextra q b))

#print axioms duration_shift
end BB6.DRegularDurationShift
