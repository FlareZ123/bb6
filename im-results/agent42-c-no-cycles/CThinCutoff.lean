import CSharpBoundBridge

namespace BB6Agent42

/-- All-time reachability of each original-machine halting diagonal target
    is decidable by a finite run whose budget is quadratic in j. -/
theorem source_thin_hit_iff_bounded (j : Nat) :
    (∃ n, sourceRun n (some (5,0,1)) = some (0,2*j,4*j+10)) ↔
    (∃ n, n < (4*j+6)*(4*j+6) ∧
      sourceRun n (some (5,0,1)) = some (0,2*j,4*j+10)) := by
  have hr : rank (0,2*j,4*j+10) = 8*j+10 := by
    simp only [rank]
    omega
  have hbudget : ((8*j+12)*(8*j+12))/4 = (4*j+6)*(4*j+6) := by
    have he : 8*j+12=2*(4*j+6) := by omega
    rw [he]
    have hh : (2*(4*j+6))*(2*(4*j+6)) = 4*((4*j+6)*(4*j+6)) := by
      calc
        (2*(4*j+6))*(2*(4*j+6)) = (2*2)*((4*j+6)*(4*j+6)) := by ac_rfl
        _ = 4*((4*j+6)*(4*j+6)) := rfl
    rw [hh]
    simp
  simpa only [hr,show 8*j+10+2=8*j+12 by omega,hbudget] using
    source_sharp_hit_target_iff_bounded (5,0,1) (0,2*j,4*j+10)

#print axioms source_thin_hit_iff_bounded
end BB6Agent42
