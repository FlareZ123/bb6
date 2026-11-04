import SourceUpstreamBridge
import SideStop

set_option maxHeartbeats 0

namespace A4UpstreamMixed192
open BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

/-- Exclusion of the full 504-cell gate directly in the unchanged published
Cryptids Machine C accelerator. The separate original-source bridge identifies
each upstream accelerated state with the checked-in CLine state. -/
theorem upstream_reach_no_504 (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres :
       (j%12=4 ∧ m%8=4) ∨
       (j%48=43 ∧ m%16=11) ∨
       (j%48=19 ∧ m%16=3) ∨
       ((j%192=16 ∧ m%64=58) ∨
        (j%192=112 ∧ m%64=26) ∨
        (j%192=64 ∧ m%64=10) ∨
        (j%192=160 ∧ m%64=42)) ∨
       ((j%192=40 ∧ m%64=2) ∨
        (j%192=136 ∧ m%64=34) ∨
        (j%192=88 ∧ m%64=18) ∨
        (j%192=184 ∧ m%64=50)))
    (hr : A4UpstreamBridge.UpReach (.B (2*j+3) k 0)) :
    False := by
  have hsource : BB6CLine.Reach (2*j+3,k,0) := by
    simpa [A4UpstreamBridge.tup] using
      (A4UpstreamBridge.transported_reach (.B (2*j+3) k 0) hr)
  exact (A4Mixed192Side.second_stop_504_mod192_excluded j m k hm heq hres) hsource

/-- This is an all-time actual upstream accelerated-blank-run statement. -/
theorem upstream_run_never_504 (j m k time : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres :
       (j%12=4 ∧ m%8=4) ∨
       (j%48=43 ∧ m%16=11) ∨
       (j%48=19 ∧ m%16=3) ∨
       ((j%192=16 ∧ m%64=58) ∨
        (j%192=112 ∧ m%64=26) ∨
        (j%192=64 ∧ m%64=10) ∨
        (j%192=160 ∧ m%64=42)) ∨
       ((j%192=40 ∧ m%64=2) ∨
        (j%192=136 ∧ m%64=34) ∨
        (j%192=88 ∧ m%64=18) ∨
        (j%192=184 ∧ m%64=50))) :
    A4UpstreamBridge.upstreamRun time ≠
      some (.B (2*j+3) k 0) := by
  intro hrun
  have hr := A4UpstreamBridge.upstreamRun_reach time (.B (2*j+3) k 0) hrun
  exact upstream_reach_no_504 j m k hm heq hres hr

#print axioms upstream_reach_no_504
#print axioms upstream_run_never_504
end A4UpstreamMixed192
