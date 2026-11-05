import MixedHighBoth
import MixedTwoSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem exp_dominates_linear_sharp (n : Nat) :
    n+11 ≤ 2^(2*n+4) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)+4=(2*n+4)+2 := by omega
      rw [he,Nat.pow_add]
      have h4 : (2:Nat)^2=4 := by decide
      rw [h4]
      omega

/-- The two high stopping cylinders have sharp maximum arbitrary-start
    incoming ancestry two: a true two-edge path exists, and there is no
    section path of length three or greater from any starting pair. -/
theorem mixed_high_m04_pair_sharp (j m k : Nat) (hm : 4≤m)
    (hpair : (m%4=0 ∧ (j+m)%32=26) ∨
             (m%4=1 ∧ (j+m)%32=2))
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧
    (∀ (start : Nat × Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+3) (some start) ≠ some (2*j+3,k)) ∧
    (∃ start : Nat × Nat,
      BB6.Agent8Section.run secNext 2 (some start)=some (2*j+3,k)) := by
  have hb : m+10≤2^(2*m+2) := by
    cases m with
    | zero => omega
    | succ n =>
        simpa only [show 2*(n+1)+2=2*n+4 by omega]
          using exp_dominates_linear_sharp n
  have hmulp : j≤2^(2*m+2)*j := by
    have hle : 1≤2^(2*m+2) := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hle
  have hmuladd : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  have hsmall : 24≤(2*j+3)+k ∧ 5≤k := by omega
  have hpow : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdiv : 256 ∣ k+j+3*m+5 := by
    rw [hstop]
    obtain ⟨v,hv⟩ := hpow
    refine ⟨v*(j+3),?_⟩
    rw [hv]
    ac_rfl
  obtain ⟨t,ht⟩ := hdiv
  have hfirst : oddLowGate (2*j+3) k := by
    simp only [oddLowGate]
    omega
  have hsecond : (let a1 := ((2*j+3)+k-4)/2
                  let k1 := ((2*j+3)+3*k-10)/4
                  BB6.Agent46.sixEvenRightGate a1 k1) := by
    simp only [BB6.Agent46.sixEvenRightGate]
    omega
  have hbad : (let a1 := ((2*j+3)+k-4)/2
               let k1 := ((2*j+3)+3*k-10)/4
               let a2 := a1+k1-2
               let k2 := (k1-2)/2
               5≤k2 ∧ k2%2=1 ∧
               ((a2+k2)%4=1 ∨ (a2+k2)%4=2)) := by
    omega
  exact ⟨mixed_high_m04_pair_halt j m k hstop,
    mixed_two_step_sharp (2*j+3) k hfirst hsecond hbad⟩

#print axioms mixed_high_m04_pair_sharp
end BB6.Agent3
