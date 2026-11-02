import SPhysicalPhase
import Init.Omega
namespace BB6.Agent9SSourceBranch
open BB6.Agent9SExp
open BB6.Agent9SPhysicalPhase

/-- The exact four S branches of Cryptids highLevelNext, projected to
    S-success versus T-transfer. -/
def sourceStep (p : Nat × Nat) : Option (Nat × Nat) :=
  let b := p.1
  let c := p.2
  let a := 2*(b/3)
  if b % 3 = 0 then some (2*a+1,c+4)
  else if b % 3 = 1 then some (2*a+5,c+6)
  else if c = 0 then none
  else some (2*a+8,c-1)

/-- The original S(b,c) macro and q=b+16 version agree on every input,
    including the event of exiting to the T section. -/
theorem source_q_step (b c : Nat) :
    stepS (b+16,c) = (sourceStep (b,c)).map (fun p => (p.1+16,p.2)) := by
  unfold stepS sourceStep
  by_cases h0 : b % 3 = 0
  · have hh : (b+16)%3=1 := by omega
    simp [h0,hh,nextQ]
    congr 1
    omega
  · by_cases h1 : b % 3 = 1
    · have hh0 : (b+16)%3≠0 := by omega
      have hh1 : (b+16)%3≠1 := by omega
      simp [h0,h1,hh0,hh1,nextQ]
      congr 1
      omega
    · have hh0 : (b+16)%3=0 := by omega
      by_cases hc : c = 0
      · simp [h0,h1,hh0,hc,nextQ]
      · simp [h0,h1,hh0,hc,nextQ]
        congr 1
        omega

def sourceRun (s : Nat × Nat) : Nat → Option (Nat × Nat)
  | 0 => some s
  | n+1 => (sourceRun s n).bind sourceStep

/-- Exact all-step conjugacy of the published S-only high-level macro
    and shifted q counters, preserving all T-transfer times. -/
theorem source_q_run (b c n : Nat) :
    runS (b+16,c) n =
    (sourceRun (b,c) n).map (fun p => (p.1+16,p.2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runS,sourceRun,ih]
    cases h : sourceRun (b,c) n with
    | none => simp
    | some p =>
      simp only [Option.map_some,Option.bind_some]
      rw [source_q_step]

/-- Original source b-coordinates of the two authentic rooted S entries
    enjoy the sharp growing gap while both sections remain in S. -/
theorem source_root_distance (a b : Nat) (u v : Nat × Nat)
    (hu : sourceRun (1,3) a = some u)
    (hv : sourceRun (125,3) b = some v) :
    (u.1 + (16+min a b) ≤ v.1) ∨
    (v.1 + (16+min a b) ≤ u.1) := by
  have hs : runS (17,3) a = some (u.1+16,u.2) := by
    simpa [hu] using source_q_run 1 3 a
  have ht : runS (141,3) b = some (v.1+16,v.2) := by
    simpa [hv] using source_q_run 125 3 b
  have hd := BB6.Agent9SPhysicalPhase.surviving_roots_distance a b _ _ hs ht
  simp only [Prod.fst] at hd
  omega

#print axioms BB6.Agent9SSourceBranch.source_root_distance
#print axioms BB6.Agent9SSourceBranch.source_q_run
#print axioms BB6.Agent9SSourceBranch.source_q_step
end BB6.Agent9SSourceBranch
