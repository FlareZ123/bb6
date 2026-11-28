import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent34Raw43B1LEE0LFM559Phase1
open BB6Coverage BB6Coverage.Agent31Pump

/-- Residual 559 table. A1 remains intentionally undefined. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true  => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true  => some (some ⟨false,true,1⟩)
  | _,_ => none

theorem first44 : ∀ L,
    run0 table 44 ⟨5,[false,true,true,false]++L,[]⟩ =
      some ⟨5,L,[false,false,false,false,false,true,true,false,false,true,true]⟩ := by
  intro L
  rfl

theorem loop15 : ∀ L R,
    run0 table 15 ⟨5,[true,true,false]++L,[false,false,false,false]++R⟩ =
      some ⟨5,L,[false,false,false,false]++[true,true,false]++R⟩ := by
  intro L R
  rfl

theorem loop14 : ∀ L R,
    run0 table 14 ⟨5,[true,false]++L,[false,false,false]++R⟩ =
      some ⟨5,L,[false,false,false]++[true,true]++R⟩ := by
  intro L R
  rfl

theorem finish57 : ∀ R,
    run0 table 57 ⟨5,[true,false,true,true,false,true,true,false,true],[false,false,false]++R⟩ =
      some ⟨4,[],[false,false,true,true,false,true,true,false,true,true,true,true]++R⟩ := by
  intro R
  rfl

/-- Exact residual-559 recurrence family, written in a turn-friendly normal form. -/
def family (n : Nat) : Z0 :=
  ⟨5,
    [false,true,true,false] ++
      rep [true,true,false] (4*n+1) ++
      rep [true,false] (2*n) ++
      [true,false,true,true,false,true,true,false,true],
    []⟩

/-- First E0 left-edge phase in the exact normal form produced by the macros. -/
def phase1 (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,true,true,false,true,true,false,true,true,true,true] ++
      rep [true,true] (2*n) ++ [false] ++
      rep [true,true,false] (4*n+1) ++
      [false,true,true,false,false,true,true]⟩

theorem to_phase1 (n : Nat) :
    run0 table (88*n+116) (family n) = some (phase1 n) := by
  let m := 4*n+1
  let j := 2*n
  let tailL : List Bool := [true,false,true,true,false,true,true,false,true]
  let tailR : List Bool := [false,true,true,false,false,true,true]
  let z1 : Z0 := ⟨5, rep [true,true,false] m ++ rep [true,false] j ++ tailL,
    [false,false,false,false] ++ tailR⟩
  let z2 : Z0 := ⟨5, rep [true,false] j ++ tailL,
    [false,false,false,false] ++ rep [true,true,false] m ++ tailR⟩
  let z3 : Z0 := ⟨5, tailL,
    [false,false,false] ++ rep [true,true] j ++ [false] ++ rep [true,true,false] m ++ tailR⟩
  have h0 : run0 table 44 (family n) = some z1 := by
    have h := first44
      (rep [true,true,false] m ++ rep [true,false] j ++ tailL)
    simpa [family,z1,m,j,tailL,tailR,List.append_assoc] using h
  have h15 : run0 table (15*m) z1 = some z2 := by
    have h := sweepL table 5 [] [false,false,false,false]
      [true,true,false] [true,true,false] 15 loop15 m
      (rep [true,false] j ++ tailL) tailR
    simpa [z1,z2,List.append_assoc] using h
  have h14 : run0 table (14*j) z2 = some z3 := by
    have h := sweepL table 5 [] [false,false,false]
      [true,false] [true,true] 14 loop14 j tailL
      ([false] ++ rep [true,true,false] m ++ tailR)
    simpa [z2,z3,List.append_assoc] using h
  have h57 : run0 table 57 z3 = some (phase1 n) := by
    have h := finish57
      (rep [true,true] j ++ [false] ++ rep [true,true,false] m ++ tailR)
    simpa [z3,phase1,m,j,tailL,tailR,List.append_assoc] using h
  have H := join0 h0 (join0 h15 (join0 h14 h57))
  have hc : 44 + (15*m + (14*j + 57)) = 88*n+116 := by
    simp [m,j]
    omega
  simpa only [hc] using H

#print axioms first44
#print axioms loop15
#print axioms loop14
#print axioms finish57
#print axioms to_phase1
end BB6.Agent34Raw43B1LEE0LFM559Phase1
