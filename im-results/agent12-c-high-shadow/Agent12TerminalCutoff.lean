import Agent12CutoffPart00
import Agent12CutoffPart01
import Agent12CutoffPart02
import Agent12CutoffPart03
import Agent12CutoffPart04
import Agent12CutoffPart05
import Agent12CutoffPart06
import Agent12CutoffPart07
import Agent12CutoffPart08
import Agent12CutoffPart09
import Agent12CutoffPart10
import Agent12CutoffPart11
import Agent12CutoffPart12
import Agent12CutoffPart13
import Agent12CutoffPart14
import M8TraceCert
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8 BB6.Agent46

private theorem endpoint0 : runFast 150052 (some (5,1)) = some (621619,213453) := certified_full_prefix.2
private theorem endpoint1 : runFast 300052 (some (5,1)) = some (1614262,242598) := by
  calc
    runFast 300052 (some (5,1)) = runFast 150000 (runFast 150052 (some (5,1))) := runFast_add 150052 150000 _
    _ = _ := by rw [endpoint0,part0]
private theorem endpoint2 : runFast 450052 (some (5,1)) = some (1698114,725093) := by
  calc
    runFast 450052 (some (5,1)) = runFast 150000 (runFast 300052 (some (5,1))) := runFast_add 300052 150000 _
    _ = _ := by rw [endpoint1,part1]
private theorem endpoint3 : runFast 600052 (some (5,1)) = some (910957,1645252) := by
  calc
    runFast 600052 (some (5,1)) = runFast 150000 (runFast 450052 (some (5,1))) := runFast_add 450052 150000 _
    _ = _ := by rw [endpoint2,part2]
private theorem endpoint4 : runFast 750052 (some (5,1)) = some (3290029,980087) := by
  calc
    runFast 750052 (some (5,1)) = runFast 150000 (runFast 600052 (some (5,1))) := runFast_add 600052 150000 _
    _ = _ := by rw [endpoint3,part3]
private theorem endpoint5 : runFast 900052 (some (5,1)) = some (5173120,564704) := by
  calc
    runFast 900052 (some (5,1)) = runFast 150000 (runFast 750052 (some (5,1))) := runFast_add 750052 150000 _
    _ = _ := by rw [endpoint4,part4]
private theorem endpoint6 : runFast 1050052 (some (5,1)) = some (1989304,2680598) := by
  calc
    runFast 1050052 (some (5,1)) = runFast 150000 (runFast 900052 (some (5,1))) := runFast_add 900052 150000 _
    _ = _ := by rw [endpoint5,part5]
private theorem endpoint7 : runFast 1200052 (some (5,1)) = some (8025054,187249) := by
  calc
    runFast 1200052 (some (5,1)) = runFast 150000 (runFast 1050052 (some (5,1))) := runFast_add 1050052 150000 _
    _ = _ := by rw [endpoint6,part6]
private theorem endpoint8 : runFast 1350052 (some (5,1)) = some (7099237,1176830) := by
  calc
    runFast 1350052 (some (5,1)) = runFast 150000 (runFast 1200052 (some (5,1))) := runFast_add 1200052 150000 _
    _ = _ := by rw [endpoint7,part7]
private theorem endpoint9 : runFast 1500052 (some (5,1)) = some (3780428,3362298) := by
  calc
    runFast 1500052 (some (5,1)) = runFast 150000 (runFast 1350052 (some (5,1))) := runFast_add 1350052 150000 _
    _ = _ := by rw [endpoint8,part8]
private theorem endpoint10 : runFast 1650052 (some (5,1)) = some (4519072,3517676) := by
  calc
    runFast 1650052 (some (5,1)) = runFast 150000 (runFast 1500052 (some (5,1))) := runFast_add 1500052 150000 _
    _ = _ := by rw [endpoint9,part9]
private theorem endpoint11 : runFast 1800052 (some (5,1)) = some (8140864,2231926) := by
  calc
    runFast 1800052 (some (5,1)) = runFast 150000 (runFast 1650052 (some (5,1))) := runFast_add 1650052 150000 _
    _ = _ := by rw [endpoint10,part10]
private theorem endpoint12 : runFast 1950052 (some (5,1)) = some (2816828,5418179) := by
  calc
    runFast 1950052 (some (5,1)) = runFast 150000 (runFast 1800052 (some (5,1))) := runFast_add 1800052 150000 _
    _ = _ := by rw [endpoint11,part11]
private theorem endpoint13 : runFast 2100052 (some (5,1)) = some (3090118,5806249) := by
  calc
    runFast 2100052 (some (5,1)) = runFast 150000 (runFast 1950052 (some (5,1))) := runFast_add 1950052 150000 _
    _ = _ := by rw [endpoint12,part12]
private theorem endpoint14 : runFast 2250052 (some (5,1)) = some (14606298,573141) := by
  calc
    runFast 2250052 (some (5,1)) = runFast 150000 (runFast 2100052 (some (5,1))) := runFast_add 2100052 150000 _
    _ = _ := by rw [endpoint13,part13]
private theorem endpoint15 : runFast 2396378 (some (5,1)) = some (7215288,4780931) := by
  calc
    runFast 2396378 (some (5,1)) = runFast 146326 (runFast 2250052 (some (5,1))) := runFast_add 2250052 146326 _
    _ = _ := by rw [endpoint14,part14]

/-- Any certified live endpoint gives an all-time terminal rank cutoff.
    Early terminal visits contradict the live endpoint; later visits violate
    source-proved mass monotonicity. -/
theorem terminal_below_live_endpoint (N a0 k0 a k : Nat)
    (hend : BB6.Agent8Section.run secNext N (some (5,1)) = some (a0,k0))
    (hstop : secNext (a,k) = none) (hrank : a+2*k < a0+2*k0) :
    ¬ ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k) := by
  rintro ⟨n,hn⟩
  by_cases hbefore : n < N
  · have hpositive : 0 < N-n := by omega
    have hterminal : BB6.Agent8Section.run secNext (N-n) (some (a,k)) = none := by
      cases hdiff : N-n with
      | zero => omega
      | succ d =>
          rw [BB6.Agent8Section.run_succ_head]
          simpa [hstop] using BB6.Agent8Section.run_none secNext d
    have hindex : n+(N-n)=N := by omega
    rw [←hindex,BB6.Agent8Section.run_add,hn,hterminal] at hend
    contradiction
  · have hindex : N+(n-N)=n := by omega
    rw [←hindex,BB6.Agent8Section.run_add,hend] at hn
    have hmon := source_section_mass_mono (n-N) a0 k0 a k hn
    omega

theorem live_endpoint_16777150 :
    BB6.Agent8Section.run secNext 2396378 (some (5,1)) = some (7215288,4780931) := by
  rw [←runFast_eq_source]
  exact endpoint15

theorem all_terminal_below_16777150 (a k : Nat)
    (hstop : secNext (a,k)=none) (hrank : a+2*k<16777150) :
    ¬ ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k) :=
  terminal_below_live_endpoint 2396378 7215288 4780931 a k live_endpoint_16777150 hstop (by omega)

#print axioms terminal_below_live_endpoint
#print axioms live_endpoint_16777150
#print axioms all_terminal_below_16777150
end BB6.Agent12TerminalCutoff
