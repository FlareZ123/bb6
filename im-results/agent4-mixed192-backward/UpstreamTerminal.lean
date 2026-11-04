import SourceUpstreamBridge
import TerminalNonparity

set_option maxHeartbeats 0
namespace A4UpstreamTerminal
open BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

/-- The pinned published Cryptids accelerator's authentic blank run
cannot visit the odd/odd terminal cylinder, at any accelerated time. -/
theorem upstream_no_side_41_31 (a k time : Nat)
    (ha : a%48=41) (hk : k%48=31) (hbig : 4≤k) :
    A4UpstreamBridge.upstreamRun time ≠ some (.B a k 0) := by
  intro h
  have hr := A4UpstreamBridge.upstreamRun_reach time (.B a k 0) h
  have hsource : BB6CLine.Reach (a,k,0) := by
    simpa [A4UpstreamBridge.tup] using
      (A4UpstreamBridge.transported_reach (.B a k 0) hr)
  exact A4Mixed192Terminal.source_no_side_41_31 a k ha hk hbig hsource

theorem upstream_no_direct_35_13_96 (a k time : Nat)
    (ha : a%48=35) (hk : k%48=13) (hs : (a+k)%192=96) :
    A4UpstreamBridge.upstreamRun time ≠ some (.B a k 0) := by
  intro h
  have hr := A4UpstreamBridge.upstreamRun_reach time (.B a k 0) h
  have hsource : BB6CLine.Reach (a,k,0) := by
    simpa [A4UpstreamBridge.tup] using
      (A4UpstreamBridge.transported_reach (.B a k 0) hr)
  exact A4Mixed192Terminal.source_no_direct_35_13_96 a k ha hk hs hsource

#print axioms upstream_no_side_41_31
#print axioms upstream_no_direct_35_13_96
end A4UpstreamTerminal
