import Agent1DrainDigitStatsSource

/-!
# Length bound for the source drain's canonical ternary word

The recursive summary emits a word whose top ternary digit is nonzero.
Combined with its exact affine value formula, this gives
3^(L-1) ≤ 2*b-1.  Therefore a mass budget b ≤ ternaryOnes(ell)
forces the actual transducer length L to be at most ell.
-/

open BB6.Agent1DrainDigitStatsSource
open BB6.Agent49ParitySource
open BB6.Agent41DrainValuationNormalForm
open BB6.Agent1SignedCoordinateNormalForm
open BB6.Agent22ExactDrainCocycleSource

namespace BB6.Agent49DrainDigitLengthBound

theorem drainDigitSummary_length_pos (b : Nat) (hb : 0 < b) :
    0 < (drainDigitSummary b).length := by
  cases b with
  | zero => omega
  | succ k =>
      simp [drainDigitSummary] <;> omega

/-- Every positive input emits a nonzero leading ternary digit. -/
theorem drainDigitSummary_value_lower :
    ∀ b : Nat, 0 < b →
      3 ^ ((drainDigitSummary b).length - 1) ≤
        (drainDigitSummary b).value := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro hb
      cases b with
      | zero => omega
      | succ k =>
          let s := drainDigitStep k
          let t := drainDigitSummary s.q
          have hs := drainDigitStep_spec k
          have hq : s.q < k + 1 := by
            have hq' : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          have hlen :
              (drainDigitSummary (k + 1)).length =
                s.v + 1 + t.length := by
            simp [drainDigitSummary, s, t]
          have hval :
              (drainDigitSummary (k + 1)).value =
                (1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value := by
            simp [drainDigitSummary, s, t]
          by_cases hq0 : s.q = 0
          · have hlen0 :
                (drainDigitSummary (k + 1)).length = s.v + 1 := by
              simpa [t, hq0, drainDigitSummary] using hlen
            have hval0 :
                (drainDigitSummary (k + 1)).value =
                  (1 + s.eps) * 3 ^ s.v := by
              simpa [t, hq0, drainDigitSummary] using hval
            rw [hlen0, hval0]
            have hpow : (s.v + 1) - 1 = s.v := by omega
            rw [hpow]
            have hfac : 1 ≤ 1 + s.eps := by omega
            have hmul := Nat.mul_le_mul_right (3 ^ s.v) hfac
            simpa using hmul
          · have htpos : 0 < t.length := by
              have h := drainDigitSummary_length_pos s.q (by omega)
              simpa [t] using h
            have hlow := ih s.q hq (by omega)
            have hpow :
                3 ^ (s.v + t.length) =
                  3 ^ (s.v + 1) * 3 ^ (t.length - 1) := by
              calc
                3 ^ (s.v + t.length) =
                    3 ^ ((s.v + 1) + (t.length - 1)) := by
                      congr 1
                      omega
                _ = 3 ^ (s.v + 1) * 3 ^ (t.length - 1) := by
                      rw [Nat.pow_add]
            have hmul :=
              Nat.mul_le_mul_left (3 ^ (s.v + 1)) hlow
            have hL : (s.v + 1 + t.length) - 1 = s.v + t.length := by
              omega
            rw [hlen, hval, hL]
            calc
              3 ^ (s.v + t.length) =
                  3 ^ (s.v + 1) * 3 ^ (t.length - 1) := hpow
              _ ≤ 3 ^ (s.v + 1) * t.value := hmul
              _ ≤ (1 + s.eps) * 3 ^ s.v +
                    3 ^ (s.v + 1) * t.value := by omega

/--
If the drain input is at most the triangular ternary mass tau(ell), then
the actual recursive word length is at most ell.
-/
theorem drainDigitSummary_length_le_of_budget
    (b ell : Nat) (hb : b ≤ ternaryOnes ell) :
    (drainDigitSummary b).length ≤ ell := by
  by_cases hb0 : b = 0
  · simp [hb0, drainDigitSummary]
  · have hbpos : 0 < b := by omega
    let L := (drainDigitSummary b).length
    have hLpos : 0 < L := by
      simpa [L] using drainDigitSummary_length_pos b hbpos
    have hlow := drainDigitSummary_value_lower b hbpos
    have hformula :
        4 * (drainDigitSummary b).value + 1 = 2 * b + 3 ^ L := by
      simpa [L] using drainDigitSummary_value_formula b
    have hpow : 3 ^ L = 3 * 3 ^ (L - 1) := by
      calc
        3 ^ L = 3 ^ ((L - 1) + 1) := by congr 1; omega
        _ = 3 ^ (L - 1) * 3 := by rw [Nat.pow_succ]
        _ = 3 * 3 ^ (L - 1) := by omega
    have hlow' : 4 * 3 ^ (L - 1) + 1 ≤ 2 * b + 3 ^ L := by
      have h := Nat.add_le_add_right (Nat.mul_le_mul_left 4 hlow) 1
      rw [hformula] at h
      exact h
    have hlow2 : 3 ^ (L - 1) ≤ 2 * b - 1 := by
      rw [hpow] at hlow'
      omega
    have hones : 2 * ternaryOnes ell + 1 = 3 ^ ell :=
      twice_ones_add_one_eq_pow ell
    have hupper : 2 * b - 1 < 3 ^ ell := by omega
    have hpowlt : 3 ^ (L - 1) < 3 ^ ell :=
      lt_of_le_of_lt hlow2 hupper
    have hexp : L - 1 < ell :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < (3 : Nat))).mp hpowlt
    omega

/--
A source drain whose input also fits the ell-th ternary mass has both
signed-coordinate corrections bounded by 34*ell+122.  This is the
mass-indexed form needed by the moving-window buffer argument.
-/
theorem drainB_digit_source_correction_interface_mass
    (b a d aa dd ell : Nat) (s : Sector) (br : Branch)
    (hbudget : b ≤ ternaryOnes a)
    (hmass : b ≤ ternaryOnes ell)
    (hdrain : drainB a b d = some (.D aa dd)) :
    (a : Int) - (aa : Int) =
      ((drainDigitSummary b).length : Int) -
        2 * ((drainDigitStats b).twos : Int) ∧
    ∃ r : Nat,
      2 * aa + dd = 2 * a + d + 3 * b + 2 * r ∧
      r = (drainDigitStats b).ones + (drainDigitStats b).twos ∧
      -(34 * (ell : Int) + 122) ≤
        corrC s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrC s br ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * (ell : Int) + 122 ∧
      -(34 * (ell : Int) + 122) ≤
        corrF s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrF s br ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * (ell : Int) + 122 := by
  have hsource :=
    drainB_digit_source_correction_interface b a d aa dd s br hbudget hdrain
  have hL := drainDigitSummary_length_le_of_budget b ell hmass
  rcases hsource with
    ⟨hdrop, r, hweighted, hcount, hClo, hChi, hFlo, hFhi⟩
  have hLint : ((drainDigitSummary b).length : Int) ≤ (ell : Int) := by
    exact_mod_cast hL
  refine ⟨hdrop, r, hweighted, hcount, ?_, ?_, ?_, ?_⟩
  · calc
      -(34 * (ell : Int) + 122) ≤
          -(34 * ((drainDigitSummary b).length : Int) + 122) := by omega
      _ ≤ corrC s br ((a : Int) - (aa : Int)) (r : Int) := hClo
  · exact le_trans hChi (by omega)
  · calc
      -(34 * (ell : Int) + 122) ≤
          -(24 * ((drainDigitSummary b).length : Int) + 84) := by omega
      _ ≤ corrF s br ((a : Int) - (aa : Int)) (r : Int) := hFlo
  · exact le_trans hFhi (by omega)

#print axioms drainDigitSummary_length_pos
#print axioms drainDigitSummary_value_lower
#print axioms drainDigitSummary_length_le_of_budget
#print axioms drainB_digit_source_correction_interface_mass

end BB6.Agent49DrainDigitLengthBound
