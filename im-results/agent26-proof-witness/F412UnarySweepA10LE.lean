import F412Partition
import UnarySweep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412UnarySweep
open BB6Coverage BB6.Agent26F412Graft
open BB6Coverage.Agent31Pump BB6Coverage.Agent1UnarySweep

/-- F412's A1=0LE, F0=0LD, B1=1LD cylinder, E1 still absent. -/
def p : PartialMachine :=
  refine (refine (fChild (6 : Fin 9) ⟨false,false,4⟩)
    (5,false) (some ⟨false,false,3⟩))
    (1,true) (some ⟨true,false,3⟩)

def pair : List Bool := [true,true]

/-- Exactly the canonical (E, 1[E0]0(11)^m) zipper configuration,
    including one additional trailing zero present in the blank entry. -/
def C (m : Nat) : Z0 :=
  ⟨4,[false,true],[false] ++ rep pair m ++ [false]⟩

/-- After sweeping the pair of adjacent zeros to the right boundary. -/
def R (m : Nat) : Z0 :=
  ⟨4,[false] ++ rep pair m ++ [true],[false,false]⟩

theorem entry : run0 p 11 ⟨0,[],[]⟩ = some (C 0) := by decide

theorem four (L R : List Bool) :
    run0 p 4 ⟨4,[false] ++ L,[false] ++ pair ++ R⟩ =
      some ⟨4,[false] ++ pair ++ L,[false] ++ R⟩ := by
  rfl

/-- Repeat the finite, uniform E0–C0–F1–A1 four-step move m times. -/
theorem sweep (m : Nat) :
    run0 p (4*m) (C m) = some (R m) := by
  have h := sweepR p (4 : Fin 6) [false] [false] pair pair 4
    (by intro L R; exact four L R) m [true] [false]
  simpa only [C,R,List.append_assoc] using h

/-- E0,C0,F0, from the right boundary to the left-going D1 sweep. -/
theorem enterD (m : Nat) :
    run0 p 3 (R m) =
      some (⟨3,rep pair (m+1) ++ [true],[false]⟩ : Z0) := by
  rfl

theorem two (L R : List Bool) :
    run0 p 2 ⟨3,pair ++ L,R⟩ =
      some ⟨3,L,pair ++ R⟩ := by
  rfl

/-- Sweep all 2m+2 ones to the left with m+1 D1/B1 pairs. -/
theorem travel (m : Nat) :
    run0 p (2*(m+1))
      ⟨3,rep pair (m+1) ++ [true],[false]⟩ =
      some ⟨3,[true],rep pair (m+1) ++ [false]⟩ := by
  have h := sweepL p (3 : Fin 6) [] [] pair pair 2
    (by intro L R; exact two L R) (m+1) [true] [false]
  simpa only [List.nil_append] using h

/-- D1 then B0,C0,F1,A1: reverse direction and grow two unary cells. -/
theorem finish (m : Nat) :
    run0 p 5 ⟨3,[true],rep pair (m+1) ++ [false]⟩ =
      some (C (m+1)) := by
  rfl

theorem next (m : Nat) :
    run0 p (6*m+10) (C m) = some (C (m+1)) := by
  have h1 := join0 (sweep m) (enterD m)
  have h2 := join0 h1 (travel m)
  have h3 := join0 h2 (finish m)
  have hn : (4*m + 3 + 2*(m+1)) + 5 = 6*m+10 := by omega
  rw [← hn]
  exact h3

/-- A source-checkable infinite-run certificate for every completion
    of E1. From the real blank configuration, enter C0 after 11 steps,
    then perform 6m+10 defined steps between each C_m and C_(m+1). -/
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let I : Z0 → Prop := fun z =>
    z = ⟨0,[],[]⟩ ∨ ∃ k, z = C k
  apply never_of_closed p I (Or.inl rfl) ?_ m hm
  intro z hz
  rcases hz with rfl | ⟨k,rfl⟩
  · exact ⟨11,C 0,by omega,entry,Or.inr ⟨0,rfl⟩⟩
  · exact ⟨6*k+10,C (k+1),by omega,next k,Or.inr ⟨k+1,rfl⟩⟩

#print axioms never

end BB6.Agent26F412UnarySweep
