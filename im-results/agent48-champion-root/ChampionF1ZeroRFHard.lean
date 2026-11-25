import SweepPumping
import F0SiblingCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48F1ZeroRFHard
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,13,11,24,14,21,3,16,12,11,14,21]
abbrev F : List Bool := [true,false,true,true,true]
abbrev W : List Bool := [false,true,false,true,true,true]
abbrev P : List Bool := [false,false,false,false,true,true]
abbrev D : List Bool := [true,true,true]
abbrev S : List Bool := [false,true]
abbrev Q0 : List Bool := [false,false,true,true,true,true,true,true]
abbrev Q1 : List Bool := [false,false,false,false,false,false,true,true,true,true]
abbrev Q2 : List Bool := [true,false,true,true,true,true]
abbrev Q3 : List Bool := [true,true,true,true,false,true,true,true]

def atStage (n : Nat) : Z0 := ⟨5,F,rep P n ++ Q0 ++ rep S n⟩
theorem entry : run0 ctr 192 ⟨0,[],[]⟩ = some (atStage 1) := rfl
theorem rightBlock (L R : List Bool) :
    run0 ctr 8 ⟨5,F++L,P++R⟩ = some ⟨5,F++W++L,R⟩ := rfl
theorem leftBlock (L R : List Bool) :
    run0 ctr 10 ⟨3,D++W++L,R⟩ = some ⟨3,D++L,P++R⟩ := rfl
theorem finish (R : List Bool) : run0 ctr 12 ⟨3,D,R⟩ = some ⟨5,F,R⟩ := rfl
theorem turn0 (L R : List Bool) :
    run0 ctr 12 ⟨5,F++L,Q0++R⟩ = some ⟨3,D++L,Q1++R⟩ := rfl
theorem turn1 (L R : List Bool) :
    run0 ctr 18 ⟨5,F++L,Q1++R⟩ = some ⟨3,D++L,P++Q2++R⟩ := rfl
theorem turn2 (L R : List Bool) :
    run0 ctr 22 ⟨5,F++L,Q2++R⟩ = some ⟨3,D++L,Q3++R⟩ := rfl
theorem turn3 (L R : List Bool) :
    run0 ctr 58 ⟨5,F++L,Q3++R⟩ = some ⟨3,D++L,Q0++S++R⟩ := rfl

-- Transfer all P blocks to the left, execute the central turn, and restore all P blocks.
theorem phase (k n : Nat) (I O R : List Bool)
    (turn : ∀ L R, run0 ctr k ⟨5,F++L,I++R⟩ = some ⟨3,D++L,O++R⟩) :
    run0 ctr (8*n+k+10*n+12) ⟨5,F,rep P n++I++R⟩ =
      some ⟨5,F,rep P n++O++R⟩ := by
  have h1 := sweepR ctr 5 F [] P W 8 (by simpa using rightBlock) n [] (I++R)
  have h2 := turn (rep W n) R
  have h3 := sweepL ctr 3 D [] W P 10 (by simpa using leftBlock) n [] (O++R)
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h3 ⊢
  have h4 := finish (rep P n++(O++R))
  exact join0 (join0 (join0 h1 h2) h3) h4

theorem phase0 (n : Nat) :
    run0 ctr (8*n+12+10*n+12) (atStage n) = some ⟨5,F,rep P n++Q1++rep S n⟩ :=
  phase 12 n Q0 Q1 (rep S n) turn0

theorem phase1 (n : Nat) :
    run0 ctr (8*n+18+10*n+12) ⟨5,F,rep P n++Q1++rep S n⟩ =
      some ⟨5,F,rep P (n+1)++Q2++rep S n⟩ := by
  have h := phase 18 n Q1 (P++Q2) (rep S n) turn1
  rw [← List.append_assoc (rep P n) P Q2, rep_snoc] at h
  exact h

theorem phase2 (n : Nat) :
    run0 ctr (8*(n+1)+22+10*(n+1)+12) ⟨5,F,rep P (n+1)++Q2++rep S n⟩ =
      some ⟨5,F,rep P (n+1)++Q3++rep S n⟩ :=
  phase 22 (n+1) Q2 Q3 (rep S n) turn2

theorem phase3 (n : Nat) :
    run0 ctr (8*(n+1)+58+10*(n+1)+12) ⟨5,F,rep P (n+1)++Q3++rep S n⟩ =
      some (atStage (n+1)) := by
  simpa only [atStage,rep,List.append_assoc] using phase 58 (n+1) Q3 (Q0++S) (rep S n) turn3

theorem stage (n : Nat) : run0 ctr (72*n+194) (atStage n) = some (atStage (n+1)) := by
  have h := join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)
  have eq : 8*n+12+10*n+12 + (8*n+18+10*n+12) + (8*(n+1)+22+10*(n+1)+12) + (8*(n+1)+58+10*(n+1)+12) = 72*n+194 := by omega
  rwa [eq] at h

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atStage (k+1)) 192
    (fun k => 72*(k+1)+194) entry (fun k => by omega)
    (fun k => stage (k+1)) m hm

#print axioms entry
#print axioms stage
#print axioms never
end BB6.Agent48F1ZeroRFHard
