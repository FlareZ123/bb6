import P130Root
import P1TwoSector

namespace BB6.Agent13P130
open BB6.Agent45TwoRoot

/-- Proposed authentic P1 critical reset exclusion for n = 466 mod 16384.
    The source bridge must be audited in full CI before claiming certification. -/
theorem critical_482_mod4096_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(482+4096*r)-2*(482+4096*r)-10) := by
  let q := 30+256*r
  have he : 16*q+2=482+4096*r := by dsimp [q]; omega
  intro hreach
  have hr : BB6.Agent1.Reach 2
      (14*2^(16*q+2)-2*(16*q+2)-10) := by
    simpa only [he] using hreach
  have htwo := (two_sector_critical_iff_feeders q (by omega)).mp hr
  rcases htwo with h0 | h1
  · exact l0_all_r_unreachable r (by simpa only [q] using h0)
  · exact l1_all_r_unreachable r (by simpa only [q] using h1)

#print axioms critical_482_mod4096_unreachable
end BB6.Agent13P130
