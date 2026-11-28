import SweepPumping

namespace BB6Coverage.Agent23Erase
open BB6Coverage Agent31Pump

/-- Two partial machines differ only in E1: 0RA (alternating erase) or
    0RE (self erase). B1 is never queried. -/
def p (b : Bool) : PartialMachine := fun (q,s) =>
  match q.val,s with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨true,true,3⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,if b then 4 else 0⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[true,true,true,true],rep [true,true] (n+1)⟩
def qErase (b : Bool) : Fin 6 := if b then 4 else 0

theorem first (b : Bool) : run0 (p b) 17 ⟨0,[],[]⟩ = some (family 0) := by
  cases b <;> decide

theorem pairR (b : Bool) (L R : List Bool) :
    run0 (p b) 2 ⟨qErase b,[true]++L,[true,true]++R⟩ =
      some ⟨qErase b,[true]++[false,false]++L,R⟩ := by cases b <;> rfl

theorem pairL (b : Bool) (L R : List Bool) :
    run0 (p b) 2 ⟨5,[false,false]++L,R⟩ =
      some ⟨5,L,[true,true]++R⟩ := by cases b <;> rfl

theorem growth (b : Bool) (n : Nat) :
    run0 (p b) (4*n+10) (family n) = some (family (n+1)) := by
  have h1 : run0 (p b) 2 (family n) =
      some ⟨qErase b,[true,false,false,true,true,true],rep [true,true] n⟩ := by
    cases b <;> rfl
  have h2 : run0 (p b) (2*n) ⟨qErase b,[true,false,false,true,true,true],rep [true,true] n⟩ =
      some ⟨qErase b,[true]++rep [false,false] n++[false,false,true,true,true],[]⟩ := by
    simpa using sweepR (p b) (qErase b) [true] [] [true,true] [false,false] 2 (pairR b) n [false,false,true,true,true] []
  have h3 : run0 (p b) 3 ⟨qErase b,[true]++rep [false,false] n++[false,false,true,true,true],[]⟩ =
      some ⟨5,[false,false]++(rep [false,false] n++[false,false,true,true,true]),[true]⟩ := by
    cases b <;> rfl
  have hz : [false,false]++(rep [false,false] n++[false,false,true,true,true]) =
      rep [false,false] (n+2)++[true,true,true] := by
    change [false,false]++(rep [false,false] n++([false,false]++[true,true,true])) = _
    rw [← List.append_assoc (rep [false,false] n) [false,false], rep_snoc]
    simp only [rep,List.append_assoc]
  rw [hz] at h3
  have h4 : run0 (p b) (2*(n+2)) ⟨5,rep [false,false] (n+2)++[true,true,true],[true]⟩ =
      some ⟨5,[true,true,true],rep [true,true] (n+2)++[true]⟩ := by
    simpa using sweepL (p b) 5 [] [] [false,false] [true,true] 2 (by intro L R; exact pairL b L R) (n+2) [true,true,true] [true]
  have ho : rep [true,true] (n+2)++[true] = [true]++rep [true,true] (n+2) := by
    exact (rotate true [true] (n+2)).symm
  rw [ho] at h4
  have h5 : run0 (p b) 1 ⟨5,[true,true,true],[true]++rep [true,true] (n+2)⟩ = some (family (n+1)) := by
    cases b <;> rfl
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 2 + 2*n + 3 + 2*(n+2) + 1 = 4*n+10 by omega] at H
  exact H

theorem never (b : Bool) (m : Machine) (hm : compatible (p b) m) :
    NeverHalts m :=
  never_of_growth (p b) family 17 (fun n => 4*n+10) (first b)
    (by intro n; omega) (growth b) m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6Coverage.Agent23Erase
