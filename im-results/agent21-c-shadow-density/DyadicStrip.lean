import DyadicReach

namespace BB6.Agent21Dyadic

/-- Exact divisibility equivalence for a *single* inverse-word letter.
    Unlike the existing open_prepend theorem, this also proves the
    converse (stripping a cost-r prefix loses exactly r modulus bits).
    It is the necessary dynamic-programming identity for comparing
    finite inverse words to the modular-cone recursion. -/
theorem word_strip_dvd_iff (s z s' z' : Int) (r n : Nat)
    (w : List Nat) (hs : s'=s+shift r)
    (hz : P r*z'=z+offset s r) :
    (P (n+r)∣z+acc s (r::w)) ↔
      (P n∣z'+acc s' w) := by
  rw [show n+r=r+n by omega,P_add,acc,←hs,←Int.add_assoc,←hz,←Int.mul_add]
  exact Int.mul_dvd_mul_iff_left (P_ne r)

/-- The same identity in a form that uses the natural cost of the tail. -/
theorem completed_strip_dvd_iff (s z s' z' : Int) (r : Nat)
    (w : List Nat) (hs : s'=s+shift r)
    (hz : P r*z'=z+offset s r) :
    (P (cost (r::w))∣z+acc s (r::w)) ↔
      (P (cost w)∣z'+acc s' w) := by
  simpa only [cost_cons,Nat.add_comm] using
    word_strip_dvd_iff s z s' z' r (cost w) w hs hz

#print axioms word_strip_dvd_iff
#print axioms completed_strip_dvd_iff
end BB6.Agent21Dyadic
