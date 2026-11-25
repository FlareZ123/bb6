import F0SiblingCover
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48F1ZeroRD
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

/-- Raw139 depth-five sibling with F/1=0RD and A/1,B/1,F/0 unassigned. -/
def ctr : PartialMachine := FAR.fromCodes [7,24,11,24,14,21,3,16,12,11,24,13]
abbrev P : List Bool := [true,false,true,true,true]
abbrev O : List Bool := [true,true,true]
abbrev h : List Bool := [true]

def atStage (n : Nat) : Z0 := ⟨5,P,rep O n ++ h⟩
theorem entry : run0 ctr 66 ⟨0,[],[]⟩ = some (atStage 2) := rfl

theorem carry (L R : List Bool) : run0 ctr 7 ⟨5,P++L,O++R⟩ = some ⟨5,P++O++L,R⟩ := rfl

theorem startReset (L : List Bool) : run0 ctr 22 ⟨5,P++L,h⟩ = some ⟨3,h++L,O++O⟩ := rfl

theorem left3 (L R : List Bool) : run0 ctr 9 ⟨3,h++O++L,R⟩ = some ⟨3,h++L,O++R⟩ := rfl

theorem finish (R : List Bool) : run0 ctr 6 ⟨3,h,O++O++R⟩ = some ⟨5,P,O++h++R⟩ := rfl

theorem rep_comm (n : Nat) : rep O n ++ (O++O) = O++O++rep O n := by
  rw [← List.append_assoc,rep_snoc, List.append_assoc,rep_snoc]
  simp only [List.append_assoc]

theorem h_comm (n : Nat) : h ++ rep O n = rep O n ++ h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change h ++ (O ++ rep O n) = (O ++ rep O n) ++ h
    calc
      _ = O ++ (h ++ rep O n) := rfl
      _ = O ++ (rep O n ++ h) := congrArg (O ++ ·) ih
      _ = _ := (List.append_assoc _ _ _).symm

theorem reset (n : Nat) : run0 ctr (22+9*n+6) ⟨5,P++rep O n,h⟩ = some (atStage (n+1)) := by
  have h₁ := startReset (rep O n)
  have h₂ := sweepL ctr 3 h [] O O 9 (by simpa using left3) n [] (O++O)
  simp only [List.nil_append,List.append_nil] at h₂
  rw [rep_comm] at h₂
  have h₃ := finish (rep O n)
  have h₄ := join0 (join0 h₁ h₂) h₃
  simp only [atStage,rep,List.append_assoc] at *
  rw [h_comm] at h₄
  exact h₄

theorem stage (n : Nat) : run0 ctr (7*n+(22+9*n+6)) (atStage n) = some (atStage (n+1)) := by
  have hs := sweepR ctr 5 P [] O O 7 (by simpa using carry) n [] h
  simp only [List.nil_append,List.append_nil] at hs
  exact join0 hs (reset n)

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atStage (k+2)) 66
    (fun k => 7*(k+2)+(22+9*(k+2)+6)) entry
    (fun k => by omega)
    (fun k => by simpa only [Nat.add_assoc,Nat.add_comm 2 1,Nat.add_assoc] using stage (k+2)) m hm

theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms stage
#print axioms never
#print axioms cover
end BB6.Agent48F1ZeroRD
