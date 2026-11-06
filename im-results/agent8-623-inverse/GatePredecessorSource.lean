import Agent49AffinePredecessorBoundsSource

/-!
A root-sensitive interface between the #623 logarithmic halting gate, the
new-to-old affine buffer, and the four finite affine predecessor envelopes.

The theorem is conditional on the predecessor lying in the new affine cone.
It does not claim that the blank-root orbit remains in that cone.
All transition statements are about the pinned original-source highLevelNext.
-/

namespace BB6.Agent8GatePredecessorSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryBufferSource
open BB6.Agent49PredecessorBoundsSource

/-- Every natural number is smaller than the next power of three. -/
theorem nat_lt_three_pow_succ (n : Nat) : n < 3^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hle : n+1 ≤ 3^(n+1) := by omega
      have hpos : 0 < 3^(n+1) := Nat.pow_pos (by decide)
      have hstep : 3^(n+1) < 3^(n+2) := by
        conv_rhs => rw [Nat.pow_succ]
        nlinarith
      omega

/-- Powers of three are monotone in their natural-number exponent. -/
theorem three_pow_mono {m n : Nat} (h : m ≤ n) : 3^m ≤ 3^n := by
  have hp : ∀ k : Nat, 1 ≤ 3^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        conv_rhs => rw [Nat.pow_succ]
        nlinarith
  have hmul := Nat.mul_le_mul_left (3^m) (hp (n-m))
  calc
    3^m = 3^m * 1 := by simp
    _ ≤ 3^m * 3^(n-m) := hmul
    _ = 3^(m+(n-m)) := by rw [Nat.pow_add]
    _ = 3^n := by rw [Nat.add_sub_of_le h]

/-- A new-cone predecessor of a state satisfying the necessary halting
logarithmic gate must already lie in the old affine cone. -/
theorem gate_parent_oldAffine (a d b e : Nat)
    (ha : a%2=0)
    (hn : newAffineCone a d)
    (hx : ¬(a=4 ∧ (d=5 ∨ d=7)))
    (hnext : highLevelNext (.D a d) = some (.D b e))
    (hgate : b≤e → 3^(e-b)≤b) :
    oldAffineCone a d := by
  by_contra ho
  have hbuffer := newAffine_to_oldRight a d b e ha hn ho hx hnext
  rcases hbuffer with ⟨hb, hside⟩
  have hgap : b+1≤e-b := by omega
  have hpow : b < 3^(e-b) :=
    lt_of_lt_of_le (nat_lt_three_pow_succ b) (three_pow_mono hgap)
  have hbe : b≤e := by omega
  exact (not_lt_of_ge (hgate hbe)) hpow

/-- The two small synthetic exceptions to the affine buffer are never
visited by the blank-root section, by the existing seven-unit root mass bound. -/
theorem blank_run_avoids_buffer_exceptions (n a d : Nat)
    (hseen : run n = some (.D a d)) :
    ¬(a=4 ∧ (d=5 ∨ d=7)) := by
  intro hx
  rcases hx with ⟨ha, hd⟩
  by_cases hn : n=0
  · subst n
    simp [run] at hseen
    omega
  · have hmass := run_grows_at_least_seven n a d hseen
    have hsmall : a+d≤11 := by omega
    have hnpos : 1≤n := Nat.one_le_iff_ne_zero.mpr hn
    omega

/-- If a blank-root transition starts in the new affine cone and its target
halts immediately, then its predecessor is in the old affine cone. -/
theorem blank_run_gate_parent_oldAffine (n a d b e : Nat)
    (hseen : run n = some (.D a d))
    (hcone : newAffineCone a d)
    (hnext : highLevelNext (.D a d) = some (.D b e))
    (hhalt : highLevelNext (.D b e) = none) :
    oldAffineCone a d := by
  have hseen' : run (n+1) = some (.D b e) := by
    change (run n).bind highLevelNext = some (.D b e)
    rw [hseen]
    exact hnext
  have hgate := blank_run_requires_log_gate (n+1) b e hseen' hhalt
  have ha := run_preserves_even n a d hseen
  have hx := blank_run_avoids_buffer_exceptions n a d hseen
  exact gate_parent_oldAffine a d b e ha hcone hx hnext hgate.2.1

/-- Every blank-root halting transition whose predecessor is in the new
affine cone has one of four explicit finite affine predecessor envelopes. -/
theorem blank_run_gate_parent_finite_envelope (n a d b e : Nat)
    (hseen : run n = some (.D a d))
    (hcone : newAffineCone a d)
    (hnext : highLevelNext (.D a d) = some (.D b e))
    (hhalt : highLevelNext (.D b e) = none) :
    (a≤b+2*d+8 ∧ 3*d+14≤e) ∨
    (a≤b+2*d+4 ∧ 3*d+8≤e) ∨
    (d≤b+2*a+1 ∧ 3*a≤e) ∨
    (d≤b+2*a+2 ∧ 2*a+5≤e) := by
  have hold := blank_run_gate_parent_oldAffine n a d b e hseen hcone hnext hhalt
  rcases hold with ⟨hd,hside⟩ | ⟨hd,hside⟩ |
      ⟨ha0,he,hd,hside⟩ | ⟨ha0,he,hd,hside⟩
  · exact Or.inl (farLeftOdd_predecessor_envelope a d b e hd (by omega) hnext)
  · exact Or.inr (Or.inl (farLeftEven_predecessor_envelope a d b e hd (by omega) hnext))
  · exact Or.inr (Or.inr (Or.inl
      (farRightOdd_predecessor_envelope a d b e ha0 he hd (by omega) hnext)))
  · exact Or.inr (Or.inr (Or.inr
      (farRightEven_predecessor_envelope a d b e ha0 he hd (by omega) hnext)))

#print axioms blank_run_gate_parent_finite_envelope

end BB6.Agent8GatePredecessorSource


/-- A fixed positive-gap base output has at most one exponent at which its
first evaluator can hit the ternary-ones residue. -/
theorem positive_gap_residue_exponent_unique
    {N A B : Nat}
    (hAB : A < B)
    (hA : N % 3^(A+1) = 3^A)
    (hB : N % 3^(B+1) = 3^B) : False := by
  have hdiv1 : 3^(A+1) ∣ 3^(B+1) := by
    obtain ⟨k, hk⟩ : ∃ k, B+1 = (A+1)+k := by omega
    refine ⟨3^k, ?_⟩
    rw [hk, Nat.pow_add]
  have hdiv2 : 3^(A+1) ∣ 3^B := by
    obtain ⟨k, hk⟩ : ∃ k, B = (A+1)+k := by omega
    refine ⟨3^k, ?_⟩
    rw [hk, Nat.pow_add]
  have hmod : N % 3^(A+1) = (N % 3^(B+1)) % 3^(A+1) := by
    rw [Nat.mod_mod_of_dvd N hdiv1]
  rw [hB, Nat.mod_eq_zero_of_dvd hdiv2] at hmod
  have hpos : 0 < 3^A := Nat.pow_pos (by decide)
  omega
