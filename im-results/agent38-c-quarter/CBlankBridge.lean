import CQuarterBridge
import CBlankImproved

namespace BB6Agent38

theorem source_blank_thin_cutoff (j n : Nat)
    (h : sourceRun n (some (5,0,1)) = some (0,2*j,4*j+10)) :
    4*n + 32*j + 46 ≤
      (8*j+10)*(8*j+11)-2*(4*j+10) := by
  rw [source_run_agrees] at h
  exact blank_thin_cutoff j n h

theorem source_blank_thin_cutoff_clean (j n : Nat)
    (h : sourceRun n (some (5,0,1)) = some (0,2*j,4*j+10)) :
    n ≤ 16*j*(j+2)+11 := by
  rw [source_run_agrees] at h
  exact blank_thin_cutoff_clean j n h

#print axioms source_blank_thin_cutoff
#print axioms source_blank_thin_cutoff_clean
end BB6Agent38
