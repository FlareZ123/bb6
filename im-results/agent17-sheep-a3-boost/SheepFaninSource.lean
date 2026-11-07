import SheepA3Boost
import SheepA6Boost
import SheepA7Boost
import SheepBoostSourceModel

namespace SheepFaninSource
open SheepBoostSourceModel

theorem a3_even_edge (s t q : Nat)
    (hq : 3^(16*t+10)*q+1=2^(2*9^s)) (hmin : 7≤q) :
    ∃ v, EvenGenericEdge 3 v (2^(2*9^s)) := by
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA3Boost.parent_even s t q hq hmin
  have hsrc : (2^(3+1)+1)*v+(2*3-3)=2^((16*t+10)+1)*q := by
    simpa [show 16*t+10+1=16*t+11 by omega] using heq
  have hqodd := odd_quotient_of_power (2*9^s) (16*t+10) q
      (by have hp : 0<(9:Nat)^s := Nat.pow_pos (by decide); omega) hq
  exact ⟨v, generic_edge_of_equation 3 v (16*t+10) q (2*9^s)
    (by decide) hvodd hvmin hqodd hsrc hq⟩

theorem a3_odd_edge (s t q : Nat)
    (hq : 3^(16*t+14)*q+1=2^(2*(3*9^s))) (hmin : 7≤q) :
    ∃ v, EvenGenericEdge 3 v (2^(2*(3*9^s))) := by
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA3Boost.parent_odd s t q hq hmin
  have hsrc : (2^(3+1)+1)*v+(2*3-3)=2^((16*t+14)+1)*q := by
    simpa [show 16*t+14+1=16*t+15 by omega] using heq
  have hqodd := odd_quotient_of_power (2*(3*9^s)) (16*t+14) q
      (by have hp : 0<(9:Nat)^s := Nat.pow_pos (by decide); omega) hq
  exact ⟨v, generic_edge_of_equation 3 v (16*t+14) q (2*(3*9^s))
    (by decide) hvodd hvmin hqodd hsrc hq⟩

theorem a6_edge (m t q : Nat)
    (hq : 3^(21*t+20)*q+1=2^(2*3^(6*m))) (hmin : 7≤q) (hq3 : q%3=0) :
    ∃ v, EvenGenericEdge 6 v (2^(2*3^(6*m))) := by
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA6Boost.parent_six m t q hq hmin hq3
  have hsrc : (2^(6+1)+1)*v+(2*6-3)=2^((21*t+20)+1)*q := by
    simpa [show 21*t+20+1=21*t+21 by omega] using heq
  have hqodd := odd_quotient_of_power (2*3^(6*m)) (21*t+20) q
      (by have hp : 0<(3:Nat)^(6*m) := Nat.pow_pos (by decide); omega) hq
  exact ⟨v, generic_edge_of_equation 6 v (21*t+20) q (2*3^(6*m))
    (by decide) hvodd hvmin hqodd hsrc hq⟩

theorem a7_even_edge (s t q : Nat)
    (hq : 3^(256*t+221)*q+1=2^(2*9^s)) (hmin : 7≤q) :
    ∃ v, EvenGenericEdge 7 v (2^(2*9^s)) := by
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA7Boost.parent_even s t q hq hmin
  have hsrc : (2^(7+1)+1)*v+(2*7-3)=2^((256*t+221)+1)*q := by
    simpa [show 256*t+221+1=256*t+222 by omega] using heq
  have hqodd := odd_quotient_of_power (2*9^s) (256*t+221) q
      (by have hp : 0<(9:Nat)^s := Nat.pow_pos (by decide); omega) hq
  exact ⟨v, generic_edge_of_equation 7 v (256*t+221) q (2*9^s)
    (by decide) hvodd hvmin hqodd hsrc hq⟩

theorem a7_odd_edge (s t q : Nat)
    (hq : 3^(256*t+83)*q+1=2^(2*(3*9^s))) (hmin : 7≤q) :
    ∃ v, EvenGenericEdge 7 v (2^(2*(3*9^s))) := by
  obtain ⟨v,hvmin,hvodd,heq⟩ := SheepA7Boost.parent_odd s t q hq hmin
  have hsrc : (2^(7+1)+1)*v+(2*7-3)=2^((256*t+83)+1)*q := by
    simpa [show 256*t+83+1=256*t+84 by omega] using heq
  have hqodd := odd_quotient_of_power (2*(3*9^s)) (256*t+83) q
      (by have hp : 0<(9:Nat)^s := Nat.pow_pos (by decide); omega) hq
  exact ⟨v, generic_edge_of_equation 7 v (256*t+83) q (2*(3*9^s))
    (by decide) hvodd hvmin hqodd hsrc hq⟩

#print axioms a3_even_edge
#print axioms a3_odd_edge
#print axioms a6_edge
#print axioms a7_even_edge
#print axioms a7_odd_edge
end SheepFaninSource
