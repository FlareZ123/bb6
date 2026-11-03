import SourceUpstreamBridge
import SourceStop

set_option maxHeartbeats 0
namespace NewCoreUpstream
open BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

theorem original_never_new_cores (a k c : Nat)
    (h : A4UpstreamBridge.UpReach (.B a k c)) :
    ¬NewCore.badC a k c ∧ ¬NewCore.badD a k c := by
  have hr : BB6CLine.Reach (a,k,c) :=
    A4UpstreamBridge.transported_reach (.B a k c) h
  exact ⟨NewCore.source_blank_never_badC _ hr,
         NewCore.source_blank_never_badD _ hr⟩

theorem original_no_four_second (j m k : Nat)
    (hsector :
      (j%48=1 ∧ (j+3*m)%96=4) ∨
      (j%48=25 ∧ (j+3*m)%96=52) ∨
      (j%48=17 ∧ (j+3*m)%96=68) ∨
      (j%48=41 ∧ (j+3*m)%96=20))
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ A4UpstreamBridge.UpReach (.B (2*j+3) k 0) := by
  intro h
  have hr := A4UpstreamBridge.transported_reach _ h
  exact NewCore.source_no_four_new_second j m k hsector heq hr

theorem original_run_never_new_cores (n a k c : Nat)
    (h : A4UpstreamBridge.upstreamRun n = some (.B a k c)) :
    ¬NewCore.badC a k c ∧ ¬NewCore.badD a k c := by
  apply original_never_new_cores
  exact A4UpstreamBridge.upstreamRun_reach n _ h

#print axioms original_never_new_cores
#print axioms original_no_four_second
#print axioms original_run_never_new_cores
end NewCoreUpstream
