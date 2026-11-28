import SweepPumping
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34M2071
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some none
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨false,false,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 :=
  ⟨2,[false,true,true,true,false,true,true,false] ++ rep [true,true] (n+1),[]⟩

def cost (n : Nat) : Nat := 12*n+43

theorem first : run0 p 57 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem startTurn (L : List Bool) :
    run0 p 16 ⟨2,[false,true,true,true,false,true,true,false,true,true] ++ L,[]⟩ =
      some ⟨0,[true,true,true,true] ++ L,[true,false,true,true,false,false,false]⟩ := by rfl

theorem leftPair (L R : List Bool) :
    run0 p 2 ⟨0,[true,true] ++ L,R⟩ = some ⟨0,L,[true,true] ++ R⟩ := by rfl

theorem leftMany (n : Nat) :
    run0 p (2*n) ⟨0,rep [true,true] n,[true,false,true,true,false,false,false]⟩ =
      some ⟨0,[],rep [true,true] n ++ [true,false,true,true,false,false,false]⟩ := by
  simpa only [List.nil_append,List.append_nil] using
    (sweepL p 0 [] [] [true,true] [true,true] 2 leftPair n [] [true,false,true,true,false,false,false])

theorem middleTurn (R : List Bool) :
    run0 p 2 ⟨0,[],[true,true] ++ R⟩ = some ⟨4,[true,false,true],R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 p 5 ⟨4,[true,false] ++ L,[true] ++ R⟩ = some ⟨4,[true,false,true] ++ L,R⟩ := by rfl

theorem rightMany (n : Nat) (L R : List Bool) :
    run0 p (5*n) ⟨4,[true,false] ++ L,rep [true] n ++ R⟩ =
      some ⟨4,[true,false] ++ rep [true] n ++ L,R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using
    (sweepR p 4 [true,false] [] [true] [true] 5 rightOne n L R)

theorem endTurn (L : List Bool) :
    run0 p 6 ⟨4,[true,false] ++ L,[false,true,true,false,false,false]⟩ =
      some ⟨2,[false,true,true,true,false,true,true,false] ++ L,[]⟩ := by rfl

theorem rep_pairs (n : Nat) : rep [true,true] n = rep [true] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega]
    simp only [rep,ih,List.cons_append,List.nil_append]

theorem growth (n : Nat) : run0 p (cost n) (family n) = some (family (n+1)) := by
  have h0 : run0 p 16 (family n) = some ⟨0,rep [true,true] (n+2),[true,false,true,true,false,false,false]⟩ := by
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append] using startTurn (rep [true,true] n)
  have h1 := leftMany (n+2)
  have h2 : run0 p 2 ⟨0,[],rep [true,true] (n+2) ++ [true,false,true,true,false,false,false]⟩ =
      some ⟨4,[true,false,true],rep [true] (2*n+3) ++ [false,true,true,false,false,false]⟩ := by
    have h := middleTurn (rep [true,true] (n+1) ++ [true,false,true,true,false,false,false])
    have he : rep [true,true] (n+1) ++ [true,false,true,true,false,false,false] =
        rep [true] (2*n+3) ++ [false,true,true,false,false,false] := by
      rw [rep_pairs,show 2*n+3=2*(n+1)+1 by omega]
      calc
        _ = (rep [true] (2*(n+1)) ++ [true]) ++ [false,true,true,false,false,false] := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = ([true] ++ rep [true] (2*(n+1))) ++ [false,true,true,false,false,false] := by rw [rep_snoc]
        _ = _ := rfl
    have h' : run0 p 2 ⟨0,[],rep [true,true] (n+2) ++ [true,false,true,true,false,false,false]⟩ =
        some ⟨4,[true,false,true],rep [true,true] (n+1) ++ [true,false,true,true,false,false,false]⟩ := by
      simpa only [rep,List.append_assoc] using h
    exact h'.trans (congrArg (fun R : List Bool => some (⟨4,[true,false,true],R⟩ : Z0)) he)
  have h3 := rightMany (2*n+3) [true] [false,true,true,false,false,false]
  have h3' : run0 p (5*(2*n+3))
      ⟨4,[true,false,true],rep [true] (2*n+3) ++ [false,true,true,false,false,false]⟩ =
      some ⟨4,[true,false] ++ rep [true,true] (n+2),[false,true,true,false,false,false]⟩ := by
    have he : rep [true] (2*n+3) ++ [true] = rep [true,true] (n+2) := by
      rw [rep_snoc,rep_pairs,show 2*(n+2)=2*n+3+1 by omega]
      rfl
    simpa only [List.append_assoc,he,List.cons_append,List.nil_append] using h3
  have h4 := endTurn (rep [true,true] (n+2))
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3') h4
  have hc : 16 + 2*(n+2) + 2 + 5*(2*n+3) + 6 = cost n := by unfold cost; omega
  rw [hc] at h
  exact h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 57 cost first (by intro n; unfold cost; omega) growth m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent50Raw34M2071
