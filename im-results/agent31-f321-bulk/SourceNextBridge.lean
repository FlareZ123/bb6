import F321Periodicity
import Lean.Elab.Tactic.Omega
namespace BB6.Agent31F321Density
/-- Exact upstream highLevelNext option-valued branch table, independently of upstream project. -/
def sourceNext (a d:Nat) : Option (Nat×Nat) :=
  if a≥d+2 then some (a-d-2,2*d+3)
  else if a=d+1 then none
  else if a=d then some (2*a+4,1)
  else if 3*a+1≤d then some (4*a+6,d-3*a)
  else if (d-a)%2=0 then some (4*a+6,2)
  else some (4*a+6,1)

theorem sourceNext_none_iff (a d:Nat) :
  sourceNext a d = none ↔ a=d+1 := by
  constructor
  · intro h
    by_cases h1:a≥d+2
    · simp [sourceNext,h1] at h
    · by_cases h2:a=d+1
      · exact h2
      · have he : (if a = d then some (2*a+4,1) else if 3*a+1≤d then some (4*a+6,d-3*a) else if (d-a)%2=0 then some (4*a+6,2) else some (4*a+6,1)) = none := by simpa [sourceNext,h1,h2] using h
        repeat (split at he); all_goals simp_all
  · intro h; subst a; simp [sourceNext]

theorem sourceNext_some_of_move {a d A D:Nat} (h:CounterMove a d A D) :
  sourceNext a d=some (A,D) := by
  cases h with
  | high d hg => simp [sourceNext,hg]
  | equal => simp [sourceNext]
  | far d ha hd =>
      simp [sourceNext,show ¬(a≥d+2) by omega,show ¬(a=d+1) by omega,show ¬(a=d) by omega,hd]
  | middleEven d ha hd hp =>
      simp [sourceNext,show ¬(a≥d+2) by omega,show ¬(a=d+1) by omega,show ¬(a=d) by omega,show ¬(3*a+1≤d) by omega,hp]
  | middleOdd d ha hd hp =>
      simp [sourceNext,show ¬(a≥d+2) by omega,show ¬(a=d+1) by omega,show ¬(a=d) by omega,show ¬(3*a+1≤d) by omega,show ¬((d-a)%2=0) by omega]

theorem move_of_sourceNext_some {a d A D:Nat}
  (h:sourceNext a d=some (A,D)) : CounterMove a d A D := by
  by_cases h1:a≥d+2
  · have hp : (a-d-2,2*d+3)=(A,D) := Option.some.inj (by simpa [sourceNext,h1] using h)
    have ha:A=a-d-2 := (Prod.mk.inj hp).1.symm
    have hd:D=2*d+3 := (Prod.mk.inj hp).2.symm
    subst A; subst D
    exact .high a d h1
  · by_cases h2:a=d+1
    · simp [sourceNext,h1,h2] at h
    · by_cases h3:a=d
      · have hctx : sourceNext a d = some (2*a+4,1) := by
          rw [h3]
          simp [sourceNext]
        have hp : (2*a+4,1)=(A,D) := Option.some.inj (hctx.symm.trans h)
        have ha:A=2*a+4 := (Prod.mk.inj hp).1.symm
        have hd:D=1 := (Prod.mk.inj hp).2.symm
        subst A; subst D; subst d
        exact .equal a
      · by_cases h4:3*a+1≤d
        · have hp : (4*a+6,d-3*a)=(A,D) := Option.some.inj (by simpa [sourceNext,h1,h2,h3,h4] using h)
          have ha:A=4*a+6 := (Prod.mk.inj hp).1.symm
          have hd:D=d-3*a := (Prod.mk.inj hp).2.symm
          subst A; subst D
          exact .far a d (by omega) h4
        · by_cases h5:(d-a)%2=0
          · have hp : (4*a+6,2)=(A,D) := Option.some.inj (by simpa [sourceNext,h1,h2,h3,h4,h5] using h)
            have ha:A=4*a+6 := (Prod.mk.inj hp).1.symm
            have hd:D=2 := (Prod.mk.inj hp).2.symm
            subst A; subst D
            exact .middleEven a d (by omega) (by omega) h5
          · have hp : (4*a+6,1)=(A,D) := Option.some.inj (by simpa [sourceNext,h1,h2,h3,h4,h5] using h)
            have ha:A=4*a+6 := (Prod.mk.inj hp).1.symm
            have hd:D=1 := (Prod.mk.inj hp).2.symm
            subst A; subst D
            exact .middleOdd a d (by omega) (by omega) (by omega)

theorem sourceNext_some_iff {a d A D:Nat} :
  sourceNext a d=some (A,D) ↔ CounterMove a d A D :=
    ⟨move_of_sourceNext_some,sourceNext_some_of_move⟩

#print axioms sourceNext_some_iff
#print axioms sourceNext_none_iff
end BB6.Agent31F321Density
