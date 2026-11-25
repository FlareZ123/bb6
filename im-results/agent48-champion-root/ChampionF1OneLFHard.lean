import F0SiblingCover
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48F1OneLFHard
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,1,11,24,14,21,3,16,12,11,3,22]
abbrev P : List Bool := [true,false,true,true]
abbrev S : List Bool := [false,true,true,true]
abbrev T : List Bool := [false,false,true,true]
abbrev Q : List Bool := [true,true,true,true]
abbrev h : List Bool := [true]
abbrev H : List Bool := [true,true]
abbrev A : List Bool := [false,false,false,false,false,false]
abbrev B : List Bool := [true,false,false,false,false]
abbrev C : List Bool := [false,false,true,true,true,true,false,false]
abbrev D : List Bool := [true,true,true,true,true,false,false]

def atPhase (a : List Bool) (k m : Nat) : Z0 := ⟨5,P++rep S k++a++rep Q m,[]⟩
theorem entry : run0 ctr 137 ⟨0,[],[]⟩ = some (atPhase A 1 1) := rfl

theorem begin (L : List Bool) : run0 ctr 9 ⟨5,P++L,[]⟩ = some ⟨3,h++S++L,H⟩ := rfl

theorem leftSweep (L R : List Bool) : run0 ctr 8 ⟨3,h++S++L,H++R⟩ = some ⟨3,h++L,H++T++R⟩ := rfl

theorem rightSweep (L R : List Bool) : run0 ctr 6 ⟨5,P++L,T++R⟩ = some ⟨5,P++S++L,R⟩ := rfl

theorem microA (L R : List Bool) : run0 ctr 6 ⟨3,h++A++L,H++R⟩ = some ⟨5,P++B++L,R⟩ := rfl

theorem microB (L R : List Bool) : run0 ctr 16 ⟨3,h++B++L,H++T++R⟩ = some ⟨5,P++C++L,R⟩ := rfl

theorem microC (L R : List Bool) : run0 ctr 6 ⟨3,h++C++L,H++R⟩ = some ⟨5,P++D++L,R⟩ := rfl

theorem microD (L R : List Bool) : run0 ctr 32 ⟨3,h++D++L,H++T++R⟩ = some ⟨5,P++A++Q++L,R⟩ := rfl

theorem prepare (k : Nat) (L : List Bool) : run0 ctr (9+8*(k+1)) ⟨5,P++rep S k++L,[]⟩ = some ⟨3,h++L,H++rep T (k+1)⟩ := by
  have hs := sweepL ctr 3 h H S T 8 leftSweep (k+1) L []
  simp only [List.append_nil] at hs
  exact join0 (begin (rep S k++L)) (by simpa only [rep,List.append_assoc] using hs)

theorem restore (k : Nat) (L : List Bool) : run0 ctr (6*k) ⟨5,P++L,rep T k⟩ = some ⟨5,P++rep S k++L,[]⟩ := by
  have hs := sweepR ctr 5 P [] T S 6 (by simpa using rightSweep) k L []
  simpa only [List.nil_append,List.append_nil] using hs

theorem stepA (k m : Nat) : run0 ctr (9+8*(k+1)+6+6*(k+1)) (atPhase A k m) = some (atPhase B (k+1) m) := by
  have hs := join0 (prepare k (A++rep Q m)) (microA (rep Q m) (rep T (k+1)))
  simpa only [atPhase,List.append_assoc] using join0 hs (restore (k+1) (B++rep Q m))

theorem stepB (k m : Nat) : run0 ctr (9+8*(k+1)+16+6*k) (atPhase B k m) = some (atPhase C k m) := by
  have hs := join0 (prepare k (B++rep Q m)) (by simpa only [rep,List.append_assoc] using microB (rep Q m) (rep T k))
  simpa only [atPhase,List.append_assoc] using join0 hs (restore k (C++rep Q m))

theorem stepC (k m : Nat) : run0 ctr (9+8*(k+1)+6+6*(k+1)) (atPhase C k m) = some (atPhase D (k+1) m) := by
  have hs := join0 (prepare k (C++rep Q m)) (microC (rep Q m) (rep T (k+1)))
  simpa only [atPhase,List.append_assoc] using join0 hs (restore (k+1) (D++rep Q m))

theorem stepD (k m : Nat) : run0 ctr (9+8*(k+1)+32+6*k) (atPhase D k m) = some (atPhase A k (m+1)) := by
  have hs := join0 (prepare k (D++rep Q m)) (by simpa only [rep,List.append_assoc] using microD (rep Q m) (rep T k))
  simpa only [atPhase,rep,List.append_assoc] using join0 hs (restore k (A++Q++rep Q m))

theorem stage (k m : Nat) : run0 ctr (56*k+196) (atPhase A k m) = some (atPhase A (k+2) (m+1)) := by
  have hs := join0 (join0 (join0 (stepA k m) (stepB (k+1) m)) (stepC (k+1) m)) (stepD (k+2) m)
  rw [show 56*k+196 = (9+8*(k+1)+6+6*(k+1)) + (9+8*(k+1+1)+16+6*(k+1)) + (9+8*(k+1+1)+6+6*(k+1+1)) + (9+8*(k+2+1)+32+6*(k+2)) by omega]
  exact hs

open BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atPhase A (1+2*k) (1+k)) 137
    (fun k => 56*(1+2*k)+196) entry (fun k => by omega)
    (fun k => by
      have hs := stage (1+2*k) (1+k)
      rw [show 1+2*(k+1)=1+2*k+2 by omega,show 1+(k+1)=1+k+1 by omega]
      exact hs) m hm

#print axioms never
#print axioms stage
end BB6.Agent48F1OneLFHard
