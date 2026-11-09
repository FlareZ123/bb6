import SweepEvenExit

namespace CascadeFastReturn

/-- A maximal factor-of-two even block ends at odd deficit or the upper
    boundary strip. There is no third terminal geometry. -/
theorem maximal_even_block_exit (D k m d : Nat)
    (hfactor : D=2^m*d)
    (_hvalid : 2*k+6≤d)
    (hmax : ∀e, 2*k+6≤e → D≠2^(m+1)*e) :
    d%2=1 ∨ d<4*k+12 := by
  by_cases hod : d%2=1
  · exact Or.inl hod
  · right
    by_cases hsmall : d < 4*k+12
    · exact hsmall
    · have heven : d%2=0 := by omega
      have he : d=2*(d/2) := by omega
      have hehalf : 2*k+6≤d/2 := by omega
      have hnext : D=2^(m+1)*(d/2) := by
        calc
          D = 2^m*d := hfactor
          _ = 2^m*(2*(d/2)) := congrArg (2^m*·) he
          _ = 2^(m+1)*(d/2) := by rw [Nat.pow_succ]; ac_rfl
      exact False.elim (hmax (d/2) hehalf hnext)

#print axioms maximal_even_block_exit
end CascadeFastReturn
