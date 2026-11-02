import FastSectionDef
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact arithmetic witness for every successful odd-first, high-branch
    predecessor of any counter output (12t,10t-1). This preserves the
    arbitrary original recursive bounce depth n. -/
theorem target_high_inverse_arithmetic (t a k : Nat)
    (ht : 1≤t) (ha : 3≤a) (hodd : a%2=1) (hhigh : a<2*k)
    (h : secNext (a,k)=some (12*t,10*t-1)) :
    ∃ n : Nat, n%2=0 ∧
      11*t=2^n*(a+3) ∧
      2*k+a+9+3*n=32*t := by
  have h0 : a≠0 := by omega
  have h1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hreg : ¬2*k≤a := by omega
  have hb : (bounce (a-1) (2*k-a+3)).2=some (12*t,10*t-1) := by
    simpa only [secNext,exactSection,if_neg h0,if_neg h1,
      if_neg hk0,if_neg hreg] using h
  have heven : (a-1)%2=0 := by omega
  obtain ⟨n,hsum,hcost⟩ :=
    bounce_even_output_invariants (2*k-a+3) (a-1) (12*t) (10*t-1)
      heven (by omega) hb
  have hbase : 2*(a-1)+8=2*(a+3) := by omega
  have hvalue : 12*t+(10*t-1)+1=22*t := by omega
  have heq : 2*(11*t)=2*(2^n*(a+3)) := by
    calc
      2*(11*t)=22*t := by omega
      _ = 12*t+(10*t-1)+1 := hvalue.symm
      _ = 2^n*(2*(a-1)+8) := hsum
      _ = 2^n*(2*(a+3)) := by rw [hbase]
      _ = 2*(2^n*(a+3)) := by ac_rfl
  have hpow : 11*t=2^n*(a+3) := by omega
  have hcost' : 2*k+a+9+3*n=32*t := by omega
  have hpar : n%2=0 := by omega
  exact ⟨n,hpar,hpow,hcost'⟩

/-- The same symbolic inverse rules out an odd index t in the
    high-branch inverse sector, independent of any finite counter cutoff. -/
theorem target_high_even_index (t a k : Nat)
    (ht : 1≤t) (ha : 3≤a) (hodd : a%2=1) (hhigh : a<2*k)
    (h : secNext (a,k)=some (12*t,10*t-1)) : t%2=0 := by
  obtain ⟨n,_,hsum,_⟩ :=
    target_high_inverse_arithmetic t a k ht ha hodd hhigh h
  have hav : a+3=2*((a+3)/2) := by omega
  have hdiv : 11*t=2*(2^n*((a+3)/2)) := by
    calc
      11*t=2^n*(a+3) := hsum
      _ = 2^n*(2*((a+3)/2)) := by rw [hav]
      _ = 2*(2^n*((a+3)/2)) := by ac_rfl
  omega

#print axioms target_high_inverse_arithmetic
#print axioms target_high_even_index
end BB6.Agent46
