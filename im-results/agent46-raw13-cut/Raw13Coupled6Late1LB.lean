import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6Late1LB
open BB6Coverage BB6Coverage.Agent31Pump

def p (d : Bool) : PartialMachine := FAR.fromCodes [7,14,11,3,2,19,if d then 18 else 8,0,21,6,24,8]
def e (d : Bool) : Nat := if d then 2 else 0
abbrev X : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev R0 (r : List Bool) : Z0 := ⟨0,[],r⟩
abbrev pad (r : List Bool) : Z0 := ⟨0,[false],r⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem rot (n : Nat) : [true] ++ rep Y n = rep X n ++ [true] := by
  simpa using rotate true [false] n

theorem rotU (n : Nat) : [true] ++ rep U n = rep U n ++ [true] := by
  simpa using rotate true [true] n

theorem ones_end (n : Nat) : [true,true,true] ++ rep U n = rep U (n+1) ++ [true] := by
  change U ++ ([true] ++ rep U n) = _
  rw [rotU]
  simp only [rep,List.append_assoc]

theorem even_out (n : Nat) : rep Y (n+1) = [false] ++ rep X n ++ [true] := by
  change [false] ++ ([true] ++ rep Y n) = _
  rw [rot]
  simp only [List.append_assoc]

theorem rPair (d : Bool) (L R : List Bool) :
    run0 (p d) 2 ⟨0,[false]++L,[]++X++R⟩ = some ⟨0,[false]++U++L,[]++R⟩ := by cases d <;> rfl

theorem lPair (d : Bool) (L R : List Bool) :
    run0 (p d) 2 ⟨0,[]++U++L,[]++R⟩ = some ⟨0,[]++L,[]++Y++R⟩ := by cases d <;> rfl

theorem right (d : Bool) (a : Nat) (R : List Bool) :
    run0 (p d) (2*a) (pad (rep X a++R)) = some ⟨0,[false]++rep U a,R⟩ := by
  simpa only [List.nil_append,List.append_nil] using sweepR (p d) 0 [false] [] X U 2 (rPair d) a [] R

theorem left (d : Bool) (a : Nat) (L R : List Bool) :
    run0 (p d) (2*a) ⟨0,rep U a++L,R⟩ = some ⟨0,L,rep Y a++R⟩ := by
  simpa only [List.nil_append] using sweepL (p d) 0 [] [] U Y 2 (lPair d) a L R

theorem unpad (d : Bool) (n : Nat) (R : List Bool) (z : Z0) (h : 0 < n)
    (hr : run0 (p d) n (pad R) = some z) : run0 (p d) n (R0 R) = some z := by
  cases n with
  | zero => omega
  | succ n => exact hr

theorem turn (d : Bool) (R : List Bool) :
    run0 (p d) (3+e d) ⟨0,[true],R⟩ = some (R0 ([true,false,true]++R)) := by cases d <;> rfl

theorem oddLeft (d : Bool) (a : Nat) (R : List Bool) :
    run0 (p d) (2*a+3+e d) ⟨0,rep U a++[true],R⟩ =
      some (R0 (rep X (a+1)++[true]++R)) := by
  have h := join0 (left d a [true] R) (turn d (rep Y a++R))
  have w : [true,false,true]++(rep Y a++R) = rep X (a+1)++[true]++R := by
    change X++([true]++(rep Y a++R)) = _
    rw [← List.append_assoc [true] (rep Y a) R,rot]
    simp only [rep,List.append_assoc]
  simpa only [w,show 2*a+(3+e d)=2*a+3+e d by omega] using h

theorem middle1 (d : Bool) (L R : List Bool) :
    run0 (p d) 6 ⟨0,[false]++L,[false,true,false,true]++R⟩ =
      some ⟨0,[true,true,true]++L,X++R⟩ := by cases d <;> rfl

theorem middle2 (d : Bool) (L R : List Bool) :
    run0 (p d) 2 ⟨0,[false]++L,U++R⟩ = some ⟨0,[true,true,true]++L,R⟩ := by cases d <;> rfl

theorem middle3 (d : Bool) (L R : List Bool) :
    run0 (p d) 5 ⟨0,[false]++L,[false,true,true]++R⟩ = some ⟨0,U++U++L,R⟩ := by cases d <;> rfl

theorem middle4 (d : Bool) (L : List Bool) :
    run0 (p d) 5 ⟨0,[false]++L,[true]⟩ = some ⟨0,U++U++L,[true]⟩ := by cases d <;> rfl

theorem middle5 (d : Bool) (L : List Bool) :
    run0 (p d) 3 ⟨0,[false]++L,[]⟩ = some ⟨0,U++L,[true]⟩ := by cases d <;> rfl

theorem middle6 (d : Bool) (L : List Bool) :
    run0 (p d) 4 ⟨0,[false]++L,[false,true]⟩ = some ⟨5,[false,false,true,true,true]++L,[]⟩ := by cases d <;> rfl

theorem macro1 (d : Bool) (a : Nat) (R : List Bool) :
    run0 (p d) (4*a+11+e d) (R0 (rep X a++[false,true,false,true]++R)) =
      some (R0 (rep X (a+2)++[true,true,false]++R)) := by
  have h := join0 (right d a ([false,true,false,true]++R)) (middle1 d (rep U a) R)
  rw [ones_end] at h
  have g := join0 h (oddLeft d (a+1) (X++R))
  apply unpad d _ _ _ (by omega)
  simpa only [List.append_assoc,show [true] ++ (X ++ R) = [true,true,false] ++ R by rfl,show 2*a+6+(2*(a+1)+3+e d)=4*a+11+e d by omega] using g

theorem macro2 (d : Bool) (a : Nat) (R : List Bool) :
    run0 (p d) (4*a+7+e d) (R0 (rep X a++U++R)) =
      some (R0 (rep X (a+2)++[true]++R)) := by
  have h := join0 (right d a (U++R)) (middle2 d (rep U a) R)
  rw [ones_end] at h
  have g := join0 h (oddLeft d (a+1) R)
  apply unpad d _ _ _ (by omega)
  simpa only [List.append_assoc,show 2*a+2+(2*(a+1)+3+e d)=4*a+7+e d by omega] using g

theorem macro3 (d : Bool) (a : Nat) (R : List Bool) :
    run0 (p d) (4*a+9) (R0 (rep X a++[false,true,true]++R)) =
      some (R0 ([false]++rep X (a+1)++[true]++R)) := by
  have h := join0 (right d a ([false,true,true]++R)) (middle3 d (rep U a) R)
  have w : U++U++rep U a = rep U (a+2)++[] := by simp only [rep,List.append_nil,List.append_assoc]
  rw [w] at h
  have g := join0 h (left d (a+2) [] R)
  apply unpad d _ _ _ (by omega)
  simpa only [even_out (a+1),List.append_assoc,List.append_nil,List.singleton_append,show 2*a+5+2*(a+2)=4*a+9 by omega] using g

theorem macro4 (d : Bool) (a : Nat) :
    run0 (p d) (4*a+9) (R0 (rep X a++[true])) =
      some (R0 ([false]++rep X (a+1)++U)) := by
  have h := join0 (right d a [true]) (middle4 d (rep U a))
  have w : U++U++rep U a = rep U (a+2)++[] := by simp only [rep,List.append_nil,List.append_assoc]
  rw [w] at h
  have g := join0 h (left d (a+2) [] [true])
  apply unpad d _ _ _ (by omega)
  simpa only [even_out (a+1),List.append_assoc,List.append_nil,List.singleton_append,show 2*a+5+2*(a+2)=4*a+9 by omega] using g

theorem macro5 (d : Bool) (a : Nat) :
    run0 (p d) (4*a+5) (R0 (rep X a)) = some (R0 ([false]++rep X a++U)) := by
  have h := join0 (right d a []) (middle5 d (rep U a))
  have w : U++rep U a = rep U (a+1)++[] := by simp only [rep,List.append_nil]
  rw [w] at h
  have g := join0 h (left d (a+1) [] [true])
  apply unpad d _ _ _ (by omega)
  simpa only [even_out a,List.append_assoc,List.append_nil,List.singleton_append,show 2*a+3+2*(a+1)=4*a+5 by omega] using g

theorem macro6 (d : Bool) (a : Nat) :
    run0 (p d) (2*a+4) (R0 (rep X a++[false,true])) =
      some ⟨5,[false,false,true,true,true]++rep U a,[]⟩ := by
  apply unpad d _ _ _ (by omega)
  exact join0 (right d a [false,true]) (middle6 d (rep U a))

def V (a b : Nat) (R : List Bool) : Z0 := R0 (rep X a++[false]++rep X b++R)

theorem pairAdvance (d : Bool) (a b : Nat) (R : List Bool) :
    run0 (p d) (8*a+26+2*e d) (V a (b+2) R) = some (V (a+5) b R) := by
  have h := macro1 d a ([false]++rep X b++R)
  have g := macro2 d (a+2) ([false,false]++rep X b++R)
  have h' : run0 (p d) (4*a+11+e d) (V a (b+2) R) =
      some (R0 (rep X (a+2)++U++([false,false]++rep X b++R))) := by
    simpa only [V,rep,List.append_assoc,X,U,List.cons_append,List.nil_append] using h
  have g' := join0 h' g
  have w : rep X (a+2+2)++[true]++([false,false]++rep X b++R) = rep X (a+5)++[false]++rep X b++R := by
    have hh : rep X (a+5) = rep X (a+2+2)++X := by
      rw [show a+5=(a+2+2)+1 by omega,rep_add]
      rfl
    rw [hh]
    simp only [List.append_assoc,X,List.cons_append,List.nil_append]
  simpa only [V,w,show 4*a+11+e d+(4*(a+2)+7+e d)=8*a+26+2*e d by omega] using g'

def cost (d : Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 8*a+26+2*e d+cost d (a+5) n

theorem repeatAdvance (d : Bool) (a n b : Nat) (R : List Bool) :
    run0 (p d) (cost d a n) (V a (2*n+b) R) = some (V (a+5*n) b R) := by
  induction n generalizing a with
  | zero => simp [cost,run0]
  | succ n ih =>
    have h := pairAdvance d a (2*n+b) R
    have g := ih (a+5)
    have H := join0 h g
    simpa only [cost,show 2*(n+1)+b=2*n+b+2 by omega,show a+5+5*n=a+5*(n+1) by omega] using H

theorem oddU (d : Bool) (a : Nat) :
    run0 (p d) (12*a+55+2*e d) (V a 1 U) = some (V 0 (a+6) U) := by
  have h := macro1 d a [true]
  have g := macro2 d (a+2) [false,true]
  have h' : run0 (p d) (4*a+11+e d) (V a 1 U) = some (R0 (rep X (a+2)++U++[false,true])) := by
    simpa only [V,rep,List.append_assoc,U,X,List.cons_append,List.nil_append,List.append_nil] using h
  have g' := join0 h' g
  have w : rep X (a+2+2)++[true]++[false,true] = rep X (a+5)++[true] := by
    have hh : rep X (a+5) = rep X (a+2+2)++X := by
      rw [show a+5=(a+2+2)+1 by omega,rep_add]; rfl
    rw [hh]
    simp only [List.append_assoc,X,List.cons_append,List.nil_append]
  rw [w] at g'
  have H := join0 g' (macro4 d (a+5))
  simpa only [V,rep,List.nil_append,show 4*a+11+e d+(4*(a+2)+7+e d)+(4*(a+5)+9)=12*a+55+2*e d by omega] using H

theorem oddOne (d : Bool) (a : Nat) :
    run0 (p d) (12*a+51+2*e d) (V a 1 [true]) = some (V 0 (a+5) U) := by
  have h := macro1 d a []
  have g := macro2 d (a+2) [false]
  have h' : run0 (p d) (4*a+11+e d) (V a 1 [true]) = some (R0 (rep X (a+2)++U++[false])) := by
    simpa only [V,rep,List.append_assoc,U,X,List.cons_append,List.nil_append,List.append_nil] using h
  have g' := join0 h' g
  have w : rep X (a+2+2)++[true]++[false] = rep X (a+5) := by
    have hh : rep X (a+5) = rep X (a+2+2)++X := by
      rw [show a+5=(a+2+2)+1 by omega,rep_add]; rfl
    rw [hh]
    simp only [List.append_assoc,X,List.cons_append,List.nil_append]
  rw [w] at g'
  have H := join0 g' (macro5 d (a+5))
  simpa only [V,rep,List.nil_append,show 4*a+11+e d+(4*(a+2)+7+e d)+(4*(a+5)+5)=12*a+51+2*e d by omega] using H

theorem evenU (d : Bool) (a : Nat) :
    run0 (p d) (4*a+9) (V a 0 U) = some (V 0 (a+1) [true]) := by
  simpa only [V,rep,List.nil_append,List.append_nil,List.append_assoc,U,List.cons_append] using macro3 d a []

theorem entry (d : Bool) : run0 (p d) (65+2*e d) (R0 []) = some (V 0 5 U) := by cases d <;> rfl

theorem trace (d : Bool) : run0 (p d) (2649126+1104*e d) (R0 []) =
    some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ := by
  have h1 := join0 (entry d) (repeatAdvance d 0 2 1 U)
  have h2 := join0 h1 (oddU d 10)
  have h3 := join0 h2 (repeatAdvance d 0 8 0 U)
  have h4 := join0 h3 (evenU d 40)
  have h5 := join0 h4 (repeatAdvance d 0 20 1 [true])
  have h6 := join0 h5 (oddOne d 100)
  have h7 := join0 h6 (repeatAdvance d 0 52 1 U)
  have h8 := join0 h7 (oddU d 260)
  have h9 := join0 h8 (repeatAdvance d 0 133 0 U)
  have h10 := join0 h9 (evenU d 665)
  have h11 := join0 h10 (repeatAdvance d 0 333 0 [true])
  have h12 := join0 h11 (macro6 d 1665)
  cases d <;> exact h12

#print axioms trace
end BB6.Agent46Raw13Coupled6Late1LB
