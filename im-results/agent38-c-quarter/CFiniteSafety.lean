import CJumpSafety
import CJumpWitness
import CBlankImproved

namespace BB6Agent38
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

/-- Every Thin gateway forces a stopping accelerator call after precisely
    4j+5 further calls, by one reset, a proved full sweep, and two guards. -/
theorem thin_halts (j : Nat) :
    run (4*j+5) (some (0,2*j,4*j+10)) = none := by
  have h1 : run 1 (some (0,2*j,4*j+10)) = some (4*j+2,2,4*j+7) := by
    simp [run,nextC]
  have h2 : run (4*j+2) (some (4*j+2,2,4*j+7)) = some (0,4*j+4,5) := by
    have hs := run_sweep (4*j+2) (4*j+2) 2 (4*j+7) (by omega) (by omega)
    have hzero : 4*j+2 - (4*j+2) = 0 := by omega
    have hsum : 2+(4*j+2) = 4*j+4 := by omega
    have hdiff : 4*j+7 - (4*j+2) = 5 := by omega
    simpa only [hzero,hsum,hdiff] using hs
  have h3 : run 1 (some (0,4*j+4,5)) = some (8*j+10,2,2) := by
    have heven : (4*j+4)%2 = 0 := by omega
    have hhalf : (4*j+4)/2 = 2*j+2 := by omega
    simp [run,nextC,heven,hhalf] <;> omega
  have h4 : run 1 (some (8*j+10,2,2)) = none := by rfl
  calc
    run (4*j+5) (some (0,2*j,4*j+10))
      = run 1 (run (4*j+4) (some (0,2*j,4*j+10))) := by
          rw [show 4*j+5 = 1+(4*j+4) by omega,run_add]
    _ = run 1 (run 1 (run (4*j+3) (some (0,2*j,4*j+10)))) := by
          rw [show 4*j+4 = 1+(4*j+3) by omega,run_add]
    _ = run 1 (run 1 (run (4*j+2) (run 1 (some (0,2*j,4*j+10))))) := by
          rw [show 4*j+3 = (4*j+2)+1 by omega,run_add]
    _ = none := by rw [h1,h2,h3,h4]

/-- A kernel-checked exact 362-shortcut partial run extends p105. -/
theorem blank_tail_start :
    run 567260543 (some (5,0,1)) = some (0,31484,62974) := by
  have hp : path 362 (72311,26600,0) = (3987968,some (0,31484,62974)) := by decide
  have hseg : run 3987968 (some (72311,26600,0)) = some (0,31484,62974) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 362 (72311,26600,0)
  have hc : run 567260543 (some (5,0,1)) =
      run 3987968 (run 563272575 (some (5,0,1))) := by
    simpa only [show 3987968+563272575=567260543 by decide] using
      run_add 3987968 563272575 (some (5,0,1))
  rw [hc,p105,hseg]

/-- Every uncompressed state over the final 62,971 calls avoids Thin. -/
theorem blank_tail_safe (i : Nat) (hi : i ≤ 62971) (t : S)
    (h : run i (some (0,31484,62974)) = some t) : ¬thinS t := by
  have hc : checkedPath 4 (0,31484,62974) =
      (true,(62971,some (2,62973,0))) := by decide
  have hs := checkedPath_safe 4 (0,31484,62974)
    (by simpa only [hc] using (show True from True.intro))
  have hh := hs i (by simpa [hc] using hi) t h
  exact hh

theorem rank_run_nondecreasing (n : Nat) (s t : S)
    (h : run n (some s) = some t) : rank s ≤ rank t := by
  induction n generalizing s t with
  | zero =>
      have he : s=t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have hr : run n (some u) = some t := by simpa [run,hs] using h
          have hstep := rank_step_mono s u hs
          have htail := ih u t hr
          omega

/-- Lean-kernel proof excludes the first 15,742 Machine C Thin gateway
    indices at EVERY finite time, not only inside the computed prefix. -/
theorem all_thin_indices_le_15741_unreachable (j : Nat) (hj : j ≤ 15741) :
    ¬ ∃ n, run n (some (5,0,1)) = some (0,2*j,4*j+10) := by
  rintro ⟨n,hn⟩
  by_cases hbefore : n ≤ 567260543
  · have hdelay : n+(4*j+5) ≤ 567323514 := by omega
    have hhalt : run (n+(4*j+5)) (some (5,0,1)) = none := by
      rw [show n+(4*j+5) = (4*j+5)+n by omega,run_add,hn,thin_halts]
    have hN : 567323514 = (567323514-(n+(4*j+5)))+(n+(4*j+5)) := by omega
    have hbad : run 567323514 (some (5,0,1)) = none := by
      rw [hN,run_add,hhalt,run_none]
    rw [blank_reaches_a2_c0] at hbad
    contradiction
  · by_cases hmid : n ≤ 567323514
    · have hafter : n = (n-567260543)+567260543 := by omega
      have hlength : n-567260543 ≤ 62971 := by omega
      have hs : run (n-567260543) (some (0,31484,62974)) =
          some (0,2*j,4*j+10) := by
        rw [hafter,run_add,blank_tail_start] at hn
        exact hn
      have hno := blank_tail_safe (n-567260543) hlength (0,2*j,4*j+10) hs
      have hyes : thinS (0,2*j,4*j+10) := by
        simp [thinS] <;> omega
      exact hno hyes
    · have hafter : n=(n-567323514)+567323514 := by omega
      have hs : run (n-567323514) (some (2,62973,0)) =
          some (0,2*j,4*j+10) := by
        rw [hafter,run_add,blank_reaches_a2_c0] at hn
        exact hn
      have hrank := rank_run_nondecreasing (n-567323514)
        (2,62973,0) (0,2*j,4*j+10) hs
      simp only [rank] at hrank
      omega

#print axioms all_thin_indices_le_15741_unreachable
#print axioms rank_run_nondecreasing
#print axioms thin_halts
#print axioms blank_tail_start
#print axioms blank_tail_safe
end BB6Agent38
