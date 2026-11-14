import Agent49FastFailureSpectrumSource
import Agent49ParitySource

/-!
Complete even-third, positive-even-first one-step failure criterion for
the original Cryptids #623 high-level map.  The far-left and diagonal
branches are direct members of the exact finite B-drain spectrum.  The
right-even branch is the disjunction of the exact first-evaluator ternary
residue and the exact downstream B-drain spectrum after that evaluator.
This classifies one-step failure for every such synthetic section state;
it does not establish that the blank-root orbit reaches or avoids them.
-/

namespace BB6.Agent49EvenSector

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49FastSpectrum

/-- The even far-left branch fails exactly on the finite B-drain spectrum. -/
theorem even_left_none_iff_spectrum (a d : Nat)
    (hd : d%2=0) (hleft : d+3≤a) :
    (highLevelNext (.D a d)=none) ↔
      a-d-2 ∈ fastSpectrum (d+2) := by
  have ha : a ≠ 0 := by omega
  have hodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have heven : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  have hbranch : highLevelNext (.D a d) =
      drainB (a-d-2) (d+2) 2 := by
    simp [highLevelNext,ha,hodd,heven]
    omega
  rw [hbranch]
  exact drain_none_iff_fastSpectrum (a-d-2) (d+2) 2

/-- The even diagonal branch is controlled by the zero-first-counter
member of the exact B-drain spectrum. -/
theorem even_diagonal_none_iff_spectrum (a d : Nat)
    (ha : a%2=0) (hd : d%2=0) (hdiag : a=d+2) :
    (highLevelNext (.D a d)=none) ↔
      0 ∈ fastSpectrum a := by
  have ha0 : a ≠ 0 := by omega
  have hodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hleft : ¬(d%2=0 ∧ a≥d+3) := by omega
  have hpar : a%2≠1 := by omega
  have hbranch : highLevelNext (.D a d) = drainB 0 a 2 := by
    simp [highLevelNext,ha0,hodd,hleft,hpar,hdiag]
  rw [hbranch]
  exact drain_none_iff_fastSpectrum 0 a 2

/-- In the even right-hand sector, a halt occurs either at the initial
evalA call (the exact ternary-ones residue), or in the subsequent drain
(the exact finite first-counter spectrum for its returned block count). -/
theorem even_right_none_iff_spectrum (a d : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=0) (hside : a≤d) :
    (highLevelNext (.D a d)=none) ↔
      (a % 3^(d+2-a) = (3^(d+1-a)-1)/2) ∨
      (∃ x b m, evalA (d+1-a) a (2*a+5)=some (x,b,m) ∧
        x ∈ fastSpectrum b) := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  have h5 : d%2≠1 := by omega
  have hbranch : highLevelNext (.D a d) =
      (evalA (d+1-a) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) := by
    simp [highLevelNext,h0,h1,h2,h3,h4,h5]
    omega
  rw [hbranch]
  constructor
  · intro hnone
    cases heval : evalA (d+1-a) a (2*a+5) with
    | none =>
        exact Or.inl
          ((evalA_none_iff_ternaryCongruence
            (d+1-a) a (2*a+5)).mp heval)
    | some p =>
        rcases p with ⟨x,b,m⟩
        simp only [heval,Option.bind_some] at hnone
        exact Or.inr ⟨x,b,m,heval,
          (drain_none_iff_fastSpectrum x b m).mp hnone⟩
  · rintro (hres | ⟨x,b,m,heval,hbad⟩)
    · have heval : evalA (d+1-a) a (2*a+5)=none :=
        (evalA_none_iff_ternaryCongruence
          (d+1-a) a (2*a+5)).mpr hres
      simp [heval]
    · have hdrain : drainB x b m=none :=
        (drain_none_iff_fastSpectrum x b m).mpr hbad
      simp [heval,hdrain]

/-- Complete one-step halting classification for every positive even
first counter and even third counter.  All three fatal mechanisms are
explicit: far-left B-drain failure, diagonal B-drain failure, and the
right-even evaluator/drain disjunction. -/
theorem even_even_none_iff_three_spectra (a d : Nat)
    (ha0 : 0<a) (ha : a%2=0) (hd : d%2=0) :
    (highLevelNext (.D a d)=none) ↔
      (d+3≤a ∧ a-d-2 ∈ fastSpectrum (d+2)) ∨
      (a=d+2 ∧ 0 ∈ fastSpectrum a) ∨
      (a≤d ∧
        ((a % 3^(d+2-a) = (3^(d+1-a)-1)/2) ∨
          (∃ x b m, evalA (d+1-a) a (2*a+5)=some (x,b,m) ∧
            x ∈ fastSpectrum b))) := by
  by_cases hleft : d+3≤a
  · rw [even_left_none_iff_spectrum a d hd hleft]
    constructor
    · intro h
      exact Or.inl ⟨hleft,h⟩
    · rintro (⟨_,h⟩ | ⟨hdiag,_⟩ | ⟨_,_⟩)
      · exact h
      · omega
      · omega
  · have hsmall : a<d+3 := by omega
    by_cases hdiag : a=d+2
    · rw [even_diagonal_none_iff_spectrum a d ha hd hdiag]
      constructor
      · intro h
        exact Or.inr (Or.inl ⟨hdiag,h⟩)
      · rintro (⟨hleft,_⟩ | ⟨_,h⟩ | ⟨_,_⟩)
        · omega
        · exact h
        · omega
    · have hside : a≤d := by omega
      rw [even_right_none_iff_spectrum a d ha0 ha hd hside]
      constructor
      · intro h
        exact Or.inr (Or.inr ⟨hside,h⟩)
      · rintro (⟨hleft,_⟩ | ⟨hdiag',_⟩ | ⟨_,h⟩)
        · omega
        · omega
        · exact h

#print axioms even_left_none_iff_spectrum
#print axioms even_diagonal_none_iff_spectrum
#print axioms even_right_none_iff_spectrum
#print axioms even_even_none_iff_three_spectra

end BB6.Agent49EvenSector
