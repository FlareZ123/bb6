import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem zero_start (k : Nat) (hk : 1≤k) :
    run 2 (some (0,k,0)) = some (0,1,2*k+1) := by
  have hfirst : BB6CLine.nextC (0,k,0)=some (1,0,2*k+2) := by
    simp [BB6CLine.nextC]
  have hsecond : BB6CLine.nextC (1,0,2*k+2)=some (0,1,2*k+1) := by
    obtain ⟨d,hd⟩ : ∃ d, 2*k+2=d+4 := ⟨2*k-2,by omega⟩
    rw [hd]
    change (some (0,1,d+3) : Option S)=some (0,1,2*k+1)
    congr 1
    simp only [Prod.mk.injEq]
    constructor
    · trivial
    · constructor
      · trivial
      · omega
  change run 1 ((some (0,k,0)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  change (some (1,0,2*k+2)).bind BB6CLine.nextC = _
  simp only [Option.bind_some,hsecond]

private theorem one_start (k : Nat) (hk : 3≤k) :
    run 3 (some (1,k,0)) = some (0,4,2*k-3) := by
  have hfirst : BB6CLine.nextC (1,k,0)=some (2,2,2*k-1) := by
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    simp [BB6CLine.nextC]
    omega
  have hh := run_high 2 2 2 (2*k-1) (by omega) (by omega)
  have hnum : 3=2+1 := rfl
  rw [hnum]
  change run 2 ((some (1,k,0)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  have hC : 2*k-1-2=2*k-3 := by omega
  simp [Nat.sub_self,hC]

/-- All-natural exact realization of the arithmetic section map. -/
theorem section_exact (a k : Nat) :
    run (secTime (a,k)) (some (a,k,0)) = (secNext (a,k)).map embed0 := by
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · subst k
      decide
    · by_cases hk1 : k=1
      · subst k
        decide
      · have hk2 : 2≤k := by omega
        have hp := zero_start k (by omega)
        have hb := bounce_exact (2*k+1) 1 (by omega)
        have hf : exactSection (0,k) =
            (2+(bounce 1 (2*k+1)).1, (bounce 1 (2*k+1)).2) := by
          simp [exactSection,hk0,hk1]
        simp only [secTime,secNext,hf,Prod.fst,Prod.snd]
        rw [run_add,hp]
        exact hb
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k; decide
      · by_cases hk1 : k=1
        · subst k; decide
        · by_cases hk2 : k=2
          · subst k; decide
          · by_cases hk3 : k=3
            · subst k; decide
            · have hk4 : 4≤k := by omega
              have hp := one_start k (by omega)
              have hb := bounce_exact (2*k-3) 4 (by omega)
              have hf : exactSection (1,k) =
                  (3+(bounce 4 (2*k-3)).1,(bounce 4 (2*k-3)).2) := by
                simp [exactSection,hk0,hk1,hk2,hk3]
              simp only [secTime,secNext,hf,Prod.fst,Prod.snd]
              rw [run_add,hp]
              exact hb
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · subst k
        have hp : run 2 (some (a,0,0)) = some (a-2,2,0) := by
          have hfirst : BB6CLine.nextC (a,0,0)=some (a-2,1,1) := by
            obtain ⟨j,rfl⟩ : ∃ j, a=j+2 := ⟨a-2,by omega⟩
            simp [BB6CLine.nextC]
          change run 1 ((some (a,0,0)).bind BB6CLine.nextC)=_
          simp only [Option.bind_some,hfirst]
          simp [run,BB6CLine.nextC]
        simpa [secTime,secNext,exactSection,ha0,ha1,embed0] using hp
      · have hkpos : 1≤k := by omega
        by_cases hd : 2*k≤a
        · have hp := section_dominant a k hkpos hd
          have hf : exactSection (a,k) = (2*k+1,some (a-2*k,2*k+2)) := by
            simp [exactSection,ha0,ha1,hk0,hd]
          simp only [secTime,secNext,hf,Prod.fst,Prod.snd]
          rw [run_eq]
          exact hp
        · have hsmall : a<2*k := by omega
          have hp := start_to_zero a k ha2 (by omega)
          have hb := bounce_exact (2*k-a+3) (a-1) (by omega)
          have hf : exactSection (a,k) =
              (a-1+(bounce (a-1) (2*k-a+3)).1,
                (bounce (a-1) (2*k-a+3)).2) := by
            simp [exactSection,ha0,ha1,hk0,hd]
          simp only [secTime,secNext,hf,Prod.fst,Prod.snd]
          rw [run_add,hp]
          exact hb

#print axioms section_exact
end BB6.Agent46
