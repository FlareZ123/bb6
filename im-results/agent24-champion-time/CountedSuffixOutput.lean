import S1CountedCarryPrefixBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42CarryPrefixBridge

set_option maxHeartbeats 1000000

/--
Exact tape effect of the counted even-counter suffix.  The suffix preserves
the entire nonpositive exterior, installs the six-cell local boundary
[0,1,1,1,0,0] on cells 1..6, extends the right unary block through
even_rightStop c + 2, and preserves the old exterior after that block.
Only the one-run premise and the boundary one at cell 6 are needed for this
tape statement; the three zero premises are needed separately for the run
theorem `even_counted_suffix_from_open`.
-/
theorem even_counted_suffix_tape_output (P : Int → Bool) (c : Nat)
    (h6 : P 6 = true)
    (hone : ∀ i : Nat, i < 3*(c+1) → P (7+(i:Int)) = true) :
    (∀ x, x ≤ 0 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = P x) ∧
    (∀ x, 1 ≤ x → x ≤ 6 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x =
        decide (x ∈ ([2,3,4] : List Int))) ∧
    (∀ x, 7 ≤ x → x ≤ even_rightStop c+2 →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = true) ∧
    (∀ x, even_rightStop c+3 ≤ x →
      (frame even_tailArea (evenOpenFinalSweepTape c P) (embed even_tailFinal)).tape x = P x) := by
  have hon : leftOnes (afterEZero P (even_rightStop c))
      (even_rightStop c) (5+3*c) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [afterEZero]
    · have hdiff : even_rightStop c-(i:Int) ≠ even_rightStop c := by omega
      have hdiff1 : even_rightStop c-(i:Int) ≠ even_rightStop c+1 := by omega
      have hdiff2 : even_rightStop c-(i:Int) ≠ even_rightStop c+2 := by omega
      simp only [afterEZero,if_neg hdiff,if_neg hdiff1,if_neg hdiff2]
      by_cases h6pos : even_rightStop c-(i:Int) = 6
      · rw [h6pos]
        exact h6
      · have hxgt : 7 ≤ even_rightStop c-(i:Int) := by
          unfold even_rightStop at *
          omega
        have hk : ∃ k : Nat,
            even_rightStop c-(i:Int) = 7+(k:Int) ∧ k < 3*(c+1) := by
          refine ⟨3*(c+1)-i,?_,?_⟩
          · have hiBound : i ≤ 3*(c+1) := by
              unfold even_rightStop at *
              omega
            unfold even_rightStop at *
            omega
          · omega
        obtain ⟨k,heq,hk⟩ := hk
        rw [heq]
        exact hone k hk
  have hright : afterEZero P (even_rightStop c)
      (even_rightStop c+1) = false := by
    have hne : even_rightStop c+1 ≠ even_rightStop c := by omega
    simp [afterEZero,hne]
  have hcount : 5+3*c = (4+3*c)+1 := by omega
  have hclosed := even_swept_closed (4+3*c)
    (afterEZero P (even_rightStop c)) (even_rightStop c)
    (by simpa [hcount] using hon) hright
  have h6coord : even_rightStop c-((4+3*c):Int) = 6 := by
    unfold even_rightStop
    omega
  have hU : evenOpenFinalSweepTape c P =
      (fun x => if x = 6 then false else
        if x = even_rightStop c+1 then true else afterEZero P (even_rightStop c) x) := by
    unfold evenOpenFinalSweepTape
    rw [hcount]
    rw [hclosed]
    funext x
    simp [h6coord]
  constructor
  · intro x hx
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    have hstop : x ≠ even_rightStop c := by omega
    have hstop1 : x ≠ even_rightStop c+1 := by omega
    have hstop2 : x ≠ even_rightStop c+2 := by omega
    have hB : afterEZero P (even_rightStop c) x = P x := by
      simp [afterEZero,hstop,hstop1,hstop2]
    rw [hU]
    simp [frame,harea,h6neq,hstop1,hB]
  constructor
  · intro x hx1 hx6
    have harea : even_tailArea x = true := by
      simp [even_tailArea]
      omega
    simp [frame,harea,embed,even_tailFinal]
  constructor
  · intro x hx7 hxupper
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    rw [hU]
    simp only [frame,harea]
    by_cases hstop1 : x = even_rightStop c+1
    · have hne : even_rightStop c+1 ≠ 6 := by omega
      simp [hstop1,hne]
    · have hB : afterEZero P (even_rightStop c) x = true := by
        by_cases hstop : x = even_rightStop c
        · simp [afterEZero,hstop]
        · by_cases hstop2 : x = even_rightStop c+2
          · simp [afterEZero,hstop2]
          · have hxlt : x < even_rightStop c := by omega
            let i : Nat := (x-7).toNat
            have hpos : 0 ≤ x-7 := by omega
            have hcast : (i:Int) = x-7 := by
              simp [i,Int.toNat_of_nonneg hpos]
            have hi : i < 3*(c+1) := by omega
            have heq : x = 7+(i:Int) := by omega
            rw [heq]
            have hstop0 : 7+(i:Int) ≠ even_rightStop c := by omega
            have hstop1' : 7+(i:Int) ≠ even_rightStop c+1 := by omega
            have hstop2' : 7+(i:Int) ≠ even_rightStop c+2 := by omega
            simp [afterEZero,hstop0,hstop1',hstop2']
            exact hone i hi
      simp [hstop1,h6neq,hB]
  · intro x hx
    have harea : even_tailArea x = false := by
      simp [even_tailArea]
      omega
    have h6neq : x ≠ 6 := by omega
    have hstop1 : x ≠ even_rightStop c+1 := by omega
    have hstop : x ≠ even_rightStop c := by omega
    have hstop2 : x ≠ even_rightStop c+2 := by omega
    have hB : afterEZero P (even_rightStop c) x = P x := by
      simp [afterEZero,hstop,hstop1,hstop2]
    rw [hU]
    simp [frame,harea,h6neq,hstop1,hB]

#print axioms even_counted_suffix_tape_output

end BB6Coverage.Agent24ChampionTime
