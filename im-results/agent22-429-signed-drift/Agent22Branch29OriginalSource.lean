import BB429Branch7Source
import Branch29BurstMod262144
import Branch29SignedFloor1M
import Lean.Elab.Tactic.Omega

/-!
# Pinned original Cryptids #429 source, stronger branch29 consequences

Transfers the exact signed/source-checked local accelerator results through
BB429SourceMod16.source_run_to_local to unchanged upstream Cryptids
sourceRun, from highLevelStart. A last-reset state satisfying the
branch-7 equation has n>=128000127 and falls in just 31 residue classes
modulo 262144. Both are necessary conditional restrictions, not halting.
-/
namespace Agent22Branch29OriginalSource
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
set_option maxHeartbeats 40000000
set_option maxRecDepth 65536

private theorem bridge (i x y q : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y))
    (hbranch : y+3=2*x) (h29 : x%32=29)
    (hq : q=x/32) :
    BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  have hx : x=32*q+29 := by omega
  have hy : y=64*q+55 := by omega
  rw [hx,hy] at hroot
  exact ⟨i,BB429SourceMod16.source_run_to_local i
    (32*q+29) (64*q+55) hroot⟩

/-- Original unmodified source: any reachable branch29 final-burst
prestate has length n in the 31-class congruence roster modulo 262144. -/
theorem source_branch29_burst_mod262144 (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y))
    (hbranch : y+3=2*x) (h29 : x%32=29) (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    n%262144∈BB429Branch29BurstMod262144.admissibleN := by
  let q := x/32
  have hr := bridge i x y q hroot hbranch h29 rfl
  have hx : x=32*q+29 := by dsimp [q]; omega
  have heq' : 128*q+3*n+131=3*2^(n+2) := by omega
  exact BB429Branch29BurstMod262144.rooted_branch29_burst_mod262144
    q n hn hr heq'

/-- Original unmodified source: the conditional last-burst floor is
128,000,127 steps, with no bound on the source-orbit time i. -/
theorem source_branch29_burst_ge128000127 (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y))
    (hbranch : y+3=2*x) (h29 : x%32=29) (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    128000127≤n := by
  let q := x/32
  have hr := bridge i x y q hroot hbranch h29 rfl
  have hx : x=32*q+29 := by dsimp [q]; omega
  have heq' : 128*q+3*n+131=3*2^(n+2) := by omega
  exact BB429Branch29SignedFloor1M.rooted_branch29_final_burst_floor128000127
    q n hn hr heq'

#print axioms source_branch29_burst_mod262144
#print axioms source_branch29_burst_ge128000127
end Agent22Branch29OriginalSource
