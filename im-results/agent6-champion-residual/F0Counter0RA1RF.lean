import F0Counter0LC
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6F0.CounterRF
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent6F0.Counter0LC (one zero stop)
def ctr : PartialMachine := refine (BB6.Agent6F0.parent ⟨false,true,0⟩) (0,true) (some ⟨true,true,5⟩)
def a : List Bool := [true,false,true,false,false]
def b : List Bool := [true,true,true,true,false]
def baseR : List Bool := [true,true,true,true,true,true,true,true,false,false,true,true,true]
def config (n : Nat) : Z0 := ⟨5,[false,false]++zero++rep one (n+2)++stop,rep b n++baseR⟩

theorem load (L R : List Bool) : run0 ctr 5 ⟨5,[false,false]++L,b++R⟩ = some ⟨5,[false,false]++a++L,R⟩ := rfl
theorem prepare (L : List Bool) : run0 ctr 74 ⟨5,[false,false]++L,baseR⟩ = some ⟨3,a++a++L,baseR⟩ := rfl
theorem unload (L R : List Bool) : run0 ctr 17 ⟨3,a++[true]++L,R⟩ = some ⟨3,[true]++L,b++R⟩ := rfl

theorem unloadN (n : Nat) (L R : List Bool) : run0 ctr (17*n) ⟨3,rep a n++[true]++L,R⟩ = some ⟨3,[true]++L,rep b n++R⟩ := by
  induction n generalizing R with
  | zero => simp [rep,run0]
  | succ n ih =>
    cases n with
    | zero => simpa [rep] using unload L R
    | succ n =>
      have h1 := unload ([false,true,false,false]++rep a n++[true]++L) R
      have h2 := ih (b++R)
      have h1' : run0 ctr 17 ⟨3,rep a (n+2)++[true]++L,R⟩ = some ⟨3,rep a (n+1)++[true]++L,b++R⟩ := by
        simpa only [rep,a,List.append_assoc,List.cons_append,List.nil_append] using h1
      have H := join0 h1' h2
      rw [Nat.mul_succ, Nat.add_comm (17*(n+1)) 17]
      have he : rep b (n+1) ++ b = b ++ rep b (n+1) := rep_snoc b (n+1)
      rw [← List.append_assoc (rep b (n+1)) b R,he] at H
      simpa only [rep,List.append_assoc] using H

theorem finish (L R : List Bool) : run0 ctr 9 ⟨3,zero++L,b++R⟩ = some ⟨5,[false,false]++zero++one++L,R⟩ := rfl

theorem growth (n : Nat) : run0 ctr (22*n+117) (config n) = some (config (n+1)) := by
  have h1 := sweepR ctr 5 [false,false] [] b a 5 load n (zero++rep one (n+2)++stop) baseR
  have h1' : run0 ctr (5*n) (config n) = some ⟨5,[false,false]++rep a n++zero++rep one (n+2)++stop,baseR⟩ := by
    simpa only [config,List.nil_append,List.append_assoc] using h1
  have h2 := prepare (rep a n++zero++rep one (n+2)++stop)
  have h2' : run0 ctr 74 ⟨5,[false,false]++rep a n++zero++rep one (n+2)++stop,baseR⟩ = some ⟨3,rep a (n+2)++zero++rep one (n+2)++stop,baseR⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3 := unloadN (n+2) ([false,false]++rep one (n+2)++stop) baseR
  have h3' : run0 ctr (17*(n+2)) ⟨3,rep a (n+2)++zero++rep one (n+2)++stop,baseR⟩ = some ⟨3,zero++rep one (n+2)++stop,rep b (n+2)++baseR⟩ := by
    simpa only [zero,List.append_assoc,List.cons_append,List.nil_append] using h3
  have h4 := finish (rep one (n+2)++stop) (rep b (n+1)++baseR)
  have h4' : run0 ctr 9 ⟨3,zero++rep one (n+2)++stop,rep b (n+2)++baseR⟩ = some (config (n+1)) := by
    simpa only [config,rep,List.append_assoc,Nat.add_assoc] using h4
  have H := join0 (join0 (join0 h1' h2') h3') h4'
  rw [show 5*n+74+17*(n+2)+9=22*n+117 by omega] at H
  exact H

theorem entry : run0 ctr 222 ⟨0,[],[]⟩ = some (config 0) := rfl
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr config 222 (fun n => 22*n+117) entry (fun n => by omega) growth m hm
theorem cover_zeroRA_oneRF (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))
#print axioms growth
#print axioms entry
#print axioms cover_zeroRA_oneRF
end BB6.Agent6F0.CounterRF
