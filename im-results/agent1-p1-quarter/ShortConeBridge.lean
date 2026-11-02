import OddConeMass
import P1InverseLog
import P1TwoSector
import QuarterGap
import ShortConeGap
namespace BB6.Agent1ShortCone
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot

/-- Original-source inverseAt never has a left generator smaller than b/4-1. -/
theorem inverseAt_four_lower (b d t k c : Nat)
    (hi : inverseAt b d t = some (k,c)) : b ≤ 4*k+4 := by
  induction t generalizing k c with
  | zero =>
    simp only [inverseAt] at hi
    split at hi
    · next hc =>
      obtain ⟨hb,hmod⟩ := hc
      have heq : (k,c)=(b/4-1,d+b/2) := Option.some.inj hi.symm
      have hk : k=b/4-1 := congrArg Prod.fst heq
      omega
    · simp at hi
  | succ t ih =>
    simp only [inverseAt] at hi
    split at hi
    · simp at hi
    · next k0 c0 heq =>
      split at hi
      · next hcond =>
        have hbefore := ih k0 c0 heq
        have heq' : (k,c)=(k0+((c0-3)/2)/2+1,(c0-3)/2) := Option.some.inj hi.symm
        have hk : k=k0+((c0-3)/2)/2+1 := congrArg Prod.fst heq'
        omega
      · simp at hi

/-- All-depth, source-connected dyadic lower bound for any odd-only inverse cone. -/
theorem odd_cone_left_bound (b0 d0 b d m:Nat)
    (h:OddCone b0 d0 b d m) :
    b0+12 ≤2^m*(b+12) := by
  induction h with
  | root => simp
  | parent b d m t k c hcone hb hb4 hd hi hk hc ih =>
    have hbase := inverseAt_four_lower b d t k c hi
    have hx : b+12 ≤2*((2*k-4)+12) := by omega
    have ht : 2 ≤ 2^(t+1) := by
      rw [Nat.pow_succ]
      have hp: 1≤2^t := Nat.one_le_pow _ _ (by decide)
      omega
    have he : b+12 ≤2^(t+1)*((2*k-4)+12) :=
      Nat.le_trans hx (Nat.mul_le_mul_right ((2*k-4)+12) ht)
    have hs := Nat.mul_le_mul_left (2^m) he
    calc
      b0+12 ≤2^m*(b+12) := ih
      _ ≤2^m*(2^(t+1)*((2*k-4)+12)) := hs
      _ =2^(m+t+1)*((2*k-4)+12) := by
         simp [Nat.pow_add, Nat.mul_assoc]

/-- Generic source specialization of the short-cone strict window,
    simultaneously covering either of the two genuine Agent45 feeder roots. -/
theorem short_root_even_gap
    (q b d m t k c : Nat) (root : Bool)
    (hq:1≤q)
    (hcone:OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0)
    (hcost:m+t+1≤8*q) :
    28*2^(16*q)<2*k+8 ∧ 2*k+8<56*2^(16*q) := by
  let u := u2 q
  have hdom:=pow16_dom q hq
  have hu:u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have hu1:1≤u := by omega
  have hpower := inverseAt_power b d t k c hi
  have hback0 := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hback:2*k+c+2*t+1=b+d := by omega
  cases root with
  | false =>
    have hm:=odd_cone_mass (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+3 := by omega
    have hh:=odd_cone_left_bound (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hleft:4*u+8≤2^m*(b+12) := by
      have hfirst : 4*u+8≤6*u-2+12 := by omega
      exact Nat.le_trans hfirst hh
    exact short_even_power_gap q u 3 m t b d k c hq (Or.inl rfl) hu hmass hleft hcost hb4 hd hc hpower hback
  | true =>
    have hm:=odd_cone_mass (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+5 := by omega
    have hh:=odd_cone_left_bound (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hleft:4*u+8≤2^m*(b+12) := by
      have hfirst : 4*u+8=4*u-4+12 := by omega
      exact hfirst ▸ hh
    exact short_even_power_gap q u 5 m t b d k c hq (Or.inr rfl) hu hmass hleft hcost hb4 hd hc hpower hback

/-- A certificate of total inverse cost at most 8q cannot end on a
    necessary 14-power even-right feeder, for either source line. -/
theorem short_root_even_not_power
    (q b d m t k c j : Nat) (root : Bool)
    (hq:1≤q)
    (hcone:OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0)
    (hcost:m+t+1≤8*q) :
    2*k+8 ≠ 14*2^j := by
  obtain ⟨hl,hr⟩ := short_root_even_gap q b d m t k c root hq hcone hb hb4 hd hi hc hcost
  intro he
  by_cases hj:j≤16*q+1
  · have hp:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj
    have hw:2^(16*q+1)=2*2^(16*q):=by rw [Nat.pow_succ]; omega
    omega
  · have hj2:16*q+2≤j:=by omega
    have hp:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj2
    have hw:2^(16*q+2)=4*2^(16*q):=by rw [Nat.pow_add]; omega
    omega

#print axioms odd_cone_left_bound
#print axioms short_root_even_gap
#print axioms short_root_even_not_power
end BB6.Agent1ShortCone
