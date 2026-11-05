import ParameterCountBridge
set_option maxHeartbeats 0
namespace CascadeAgent7OddCount
open Classical CascadeAgent44

/-- Include the isolated k=0, q=7 branch in the odd parameter band. -/
def FullOddBand (q:Nat):Prop := q=7 ∨ BandOdd q

/-- The very last permissible three-adic valuation parameter is precisely
    an admissible source dyadic band, including the exceptional small q=7. -/
theorem terminal_odd_param_iff (u n d:Nat) (hd:d%2=1)
    (hz:2*u+5=3^(n+1)*d):
    OddParam u n ↔ FullOddBand (2^n*d):=by
  have hpow:0<3^(n+1):=Nat.pow_pos (by decide)
  constructor
  · rintro ⟨k,d',hd',hb,hz'⟩
    have hdEq:d'=d:=by
      apply Nat.mul_left_cancel hpow
      calc
        3^(n+1)*d'=2*u+5:=hz'.symm
        _=3^(n+1)*d:=hz
    subst d'
    cases k with
    | zero =>
      left
      simp only [Nat.pow_zero,Nat.mul_one] at hb
      omega
    | succ k =>
      right
      refine ⟨k+1,(by omega),?_,?_⟩
      · exact hb.1
      · exact hb.2
  · intro hb
    rcases hb with h7|⟨k,hk,hlo,hhi⟩
    · refine ⟨0,d,hd,?_,hz⟩
      simp only [Nat.pow_zero,Nat.mul_one]
      omega
    · exact ⟨k,d,hd,⟨hlo,hhi⟩,hz⟩

/-- Exact number of permitted odd-valuation *labels* from the complete
    3-adic factorization of 2u+5. These labels are source FirstInverseComplete
    odd parameters; distinct-parent cardinality requires separate injectivity. -/
noncomputable def fullOddParameterCount (u n:Nat):Nat:=by
  classical
  exact oddParameterCount u n + (if OddParam u n then 1 else 0)

/-- Complete all-input closed formula for the number of source-grammatical
    odd inverse valuation parameters. -/
theorem full_odd_param_count_add (u n d:Nat) (hd:d%2=1)
    (hz:2*u+5=3^(n+1)*d):
    fullOddParameterCount u n + (3^n*d).log2 +
      (if 0<n ∧ d=1 then 1 else 0) =
      2*n+d.log2+(if FullOddBand (2^n*d) then 1 else 0):=by
  classical
  have hbase:=exact_nonterminal_odd_param_count u n d hd hz
  have hterm:=terminal_odd_param_iff u n d hd hz
  have hbool:(if OddParam u n then (1:Nat) else 0)=
    (if FullOddBand (2^n*d) then 1 else 0):=by
    by_cases h:OddParam u n
    · have h':FullOddBand (2^n*d):=hterm.mp h
      simp [h,h']
    · have h':¬FullOddBand (2^n*d):=by
        intro hb
        exact h (hterm.mpr hb)
      simp [h,h']
  dsimp [fullOddParameterCount]
  rw [hbool]
  omega

/-- Subtraction-form statement, matching the closed count in Agent 44's
    ExactCount.md with V=n+1, including the final q=7 exception. -/
theorem full_odd_param_count_sub (u n d:Nat) (hd:d%2=1)
    (hz:2*u+5=3^(n+1)*d):
    fullOddParameterCount u n =
      (2*n+d.log2 - (3^n*d).log2 - (if 0<n ∧ d=1 then 1 else 0))+
      (if FullOddBand (2^n*d) then 1 else 0):=by
  classical
  have hbase:=exact_nonterminal_odd_param_count u n d hd hz
  have hterm:=terminal_odd_param_iff u n d hd hz
  have hbool:(if OddParam u n then (1:Nat) else 0)=
    (if FullOddBand (2^n*d) then 1 else 0):=by
    by_cases h:OddParam u n
    · have h':FullOddBand (2^n*d):=hterm.mp h
      simp [h,h']
    · have h':¬FullOddBand (2^n*d):=by
        intro hb
        exact h (hterm.mpr hb)
      simp [h,h']
  dsimp [fullOddParameterCount]
  rw [hbool]
  omega

#print axioms terminal_odd_param_iff
#print axioms full_odd_param_count_add
#print axioms full_odd_param_count_sub
end CascadeAgent7OddCount
