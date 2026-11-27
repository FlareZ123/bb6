import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6LateCore
open BB6Coverage BB6Coverage.Agent31Pump

def p (d : Bool) (v : Nat) : PartialMachine := FAR.fromCodes [7,14,11,3,2,19,if d then 18 else 8,0,21,v,24,8]
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

theorem rPair (d : Bool) (v : Nat) (L R : List Bool) :
    run0 (p d v) 2 ⟨0,[false]++L,[]++X++R⟩ = some ⟨0,[false]++U++L,[]++R⟩ := by cases d <;> rfl

theorem lPair (d : Bool) (v : Nat) (L R : List Bool) :
    run0 (p d v) 2 ⟨0,[]++U++L,[]++R⟩ = some ⟨0,[]++L,[]++Y++R⟩ := by cases d <;> rfl

theorem right (d : Bool) (v : Nat) (a : Nat) (R : List Bool) :
    run0 (p d v) (2*a) (pad (rep X a++R)) = some ⟨0,[false]++rep U a,R⟩ := by
  simpa only [List.nil_append,List.append_nil] using sweepR (p d v) 0 [false] [] X U 2 (rPair d v) a [] R

theorem left (d : Bool) (v : Nat) (a : Nat) (L R : List Bool) :
    run0 (p d v) (2*a) ⟨0,rep U a++L,R⟩ = some ⟨0,L,rep Y a++R⟩ := by
  simpa only [List.nil_append] using sweepL (p d v) 0 [] [] U Y 2 (lPair d v) a L R

theorem unpad (d : Bool) (v : Nat) (n : Nat) (R : List Bool) (z : Z0) (h : 0 < n)
    (hr : run0 (p d v) n (pad R) = some z) : run0 (p d v) n (R0 R) = some z := by
  cases n with
  | zero => omega
  | succ n => exact hr

theorem turn (d : Bool) (v : Nat) (R : List Bool) :
    run0 (p d v) (3+e d) ⟨0,[true],R⟩ = some (R0 ([true,false,true]++R)) := by cases d <;> rfl

theorem oddLeft (d : Bool) (v : Nat) (a : Nat) (R : List Bool) :
    run0 (p d v) (2*a+3+e d) ⟨0,rep U a++[true],R⟩ =
      some (R0 (rep X (a+1)++[true]++R)) := by
  have h := join0 (left d v a [true] R) (turn d v (rep Y a++R))
  have w : [true,false,true]++(rep Y a++R) = rep X (a+1)++[true]++R := by
    change X++([true]++(rep Y a++R)) = _
    rw [← List.append_assoc [true] (rep Y a) R,rot]
    simp only [rep,List.append_assoc]
  simpa only [w,show 2*a+(3+e d)=2*a+3+e d by omega] using h

theorem middle1 (d : Bool) (v : Nat) (L R : List Bool) :
    run0 (p d v) 6 ⟨0,[false]++L,[false,true,false,true]++R⟩ =
      some ⟨0,[true,true,true]++L,X++R⟩ := by cases d <;> rfl

theorem middle2 (d : Bool) (v : Nat) (L R : List Bool) :
    run0 (p d v) 2 ⟨0,[false]++L,U++R⟩ = some ⟨0,[true,true,true]++L,R⟩ := by cases d <;> rfl

theorem middle4 (d : Bool) (v : Nat) (L : List Bool) :
    run0 (p d v) 5 ⟨0,[false]++L,[true]⟩ = some ⟨0,U++U++L,[true]⟩ := by cases d <;> rfl

theorem middle5 (d : Bool) (v : Nat) (L : List Bool) :
    run0 (p d v) 3 ⟨0,[false]++L,[]⟩ = some ⟨0,U++L,[true]⟩ := by cases d <;> rfl

theorem middle6 (d : Bool) (v : Nat) (L : List Bool) :
    run0 (p d v) 4 ⟨0,[false]++L,[false,true]⟩ = some ⟨5,[false,false,true,true,true]++L,[]⟩ := by cases d <;> rfl

theorem macro1 (d : Bool) (v : Nat) (a : Nat) (R : List Bool) :
    run0 (p d v) (4*a+11+e d) (R0 (rep X a++[false,true,false,true]++R)) =
      some (R0 (rep X (a+2)++[true,true,false]++R)) := by
  have h := join0 (right d v a ([false,true,false,true]++R)) (middle1 d v (rep U a) R)
  rw [ones_end] at h
  have g := join0 h (oddLeft d v (a+1) (X++R))
  apply unpad d v _ _ _ (by omega)
  simpa only [List.append_assoc,show [true] ++ (X ++ R) = [true,true,false] ++ R by rfl,show 2*a+6+(2*(a+1)+3+e d)=4*a+11+e d by omega] using g

theorem macro2 (d : Bool) (v : Nat) (a : Nat) (R : List Bool) :
    run0 (p d v) (4*a+7+e d) (R0 (rep X a++U++R)) =
      some (R0 (rep X (a+2)++[true]++R)) := by
  have h := join0 (right d v a (U++R)) (middle2 d v (rep U a) R)
  rw [ones_end] at h
  have g := join0 h (oddLeft d v (a+1) R)
  apply unpad d v _ _ _ (by omega)
  simpa only [List.append_assoc,show 2*a+2+(2*(a+1)+3+e d)=4*a+7+e d by omega] using g

theorem macro4 (d : Bool) (v : Nat) (a : Nat) :
    run0 (p d v) (4*a+9) (R0 (rep X a++[true])) =
      some (R0 ([false]++rep X (a+1)++U)) := by
  have h := join0 (right d v a [true]) (middle4 d v (rep U a))
  have w : U++U++rep U a = rep U (a+2)++[] := by simp only [rep,List.append_nil,List.append_assoc]
  rw [w] at h
  have g := join0 h (left d v (a+2) [] [true])
  apply unpad d v _ _ _ (by omega)
  simpa only [even_out (a+1),List.append_assoc,List.append_nil,List.singleton_append,show 2*a+5+2*(a+2)=4*a+9 by omega] using g

theorem macro5 (d : Bool) (v : Nat) (a : Nat) :
    run0 (p d v) (4*a+5) (R0 (rep X a)) = some (R0 ([false]++rep X a++U)) := by
  have h := join0 (right d v a []) (middle5 d v (rep U a))
  have w : U++rep U a = rep U (a+1)++[] := by simp only [rep,List.append_nil]
  rw [w] at h
  have g := join0 h (left d v (a+1) [] [true])
  apply unpad d v _ _ _ (by omega)
  simpa only [even_out a,List.append_assoc,List.append_nil,List.singleton_append,show 2*a+3+2*(a+1)=4*a+5 by omega] using g

theorem macro6 (d : Bool) (v : Nat) (a : Nat) :
    run0 (p d v) (2*a+4) (R0 (rep X a++[false,true])) =
      some ⟨5,[false,false,true,true,true]++rep U a,[]⟩ := by
  apply unpad d v _ _ _ (by omega)
  exact join0 (right d v a [false,true]) (middle6 d v (rep U a))

def V (a b : Nat) (R : List Bool) : Z0 := R0 (rep X a++[false]++rep X b++R)

theorem pairAdvance (d : Bool) (v : Nat) (a b : Nat) (R : List Bool) :
    run0 (p d v) (8*a+26+2*e d) (V a (b+2) R) = some (V (a+5) b R) := by
  have h := macro1 d v a ([false]++rep X b++R)
  have g := macro2 d v (a+2) ([false,false]++rep X b++R)
  have h' : run0 (p d v) (4*a+11+e d) (V a (b+2) R) =
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

theorem repeatAdvance (d : Bool) (v : Nat) (a n b : Nat) (R : List Bool) :
    run0 (p d v) (cost d a n) (V a (2*n+b) R) = some (V (a+5*n) b R) := by
  induction n generalizing a with
  | zero => simp [cost,run0]
  | succ n ih =>
    have h := pairAdvance d v a (2*n+b) R
    have g := ih (a+5)
    have H := join0 h g
    simpa only [cost,show 2*(n+1)+b=2*n+b+2 by omega,show a+5+5*n=a+5*(n+1) by omega] using H

theorem oddU (d : Bool) (v : Nat) (a : Nat) :
    run0 (p d v) (12*a+55+2*e d) (V a 1 U) = some (V 0 (a+6) U) := by
  have h := macro1 d v a [true]
  have g := macro2 d v (a+2) [false,true]
  have h' : run0 (p d v) (4*a+11+e d) (V a 1 U) = some (R0 (rep X (a+2)++U++[false,true])) := by
    simpa only [V,rep,List.append_assoc,U,X,List.cons_append,List.nil_append,List.append_nil] using h
  have g' := join0 h' g
  have w : rep X (a+2+2)++[true]++[false,true] = rep X (a+5)++[true] := by
    have hh : rep X (a+5) = rep X (a+2+2)++X := by
      rw [show a+5=(a+2+2)+1 by omega,rep_add]; rfl
    rw [hh]
    simp only [List.append_assoc,X,List.cons_append,List.nil_append]
  rw [w] at g'
  have H := join0 g' (macro4 d v (a+5))
  simpa only [V,rep,List.nil_append,show 4*a+11+e d+(4*(a+2)+7+e d)+(4*(a+5)+9)=12*a+55+2*e d by omega] using H

theorem oddOne (d : Bool) (v : Nat) (a : Nat) :
    run0 (p d v) (12*a+51+2*e d) (V a 1 [true]) = some (V 0 (a+5) U) := by
  have h := macro1 d v a []
  have g := macro2 d v (a+2) [false]
  have h' : run0 (p d v) (4*a+11+e d) (V a 1 [true]) = some (R0 (rep X (a+2)++U++[false])) := by
    simpa only [V,rep,List.append_assoc,U,X,List.cons_append,List.nil_append,List.append_nil] using h
  have g' := join0 h' g
  have w : rep X (a+2+2)++[true]++[false] = rep X (a+5) := by
    have hh : rep X (a+5) = rep X (a+2+2)++X := by
      rw [show a+5=(a+2+2)+1 by omega,rep_add]; rfl
    rw [hh]
    simp only [List.append_assoc,X,List.cons_append,List.nil_append]
  rw [w] at g'
  have H := join0 g' (macro5 d v (a+5))
  simpa only [V,rep,List.nil_append,show 4*a+11+e d+(4*(a+2)+7+e d)+(4*(a+5)+5)=12*a+51+2*e d by omega] using H

theorem middle3B (d : Bool) (L R : List Bool) :
    run0 (p d 6) 5 ⟨0,[false]++L,[false,true,true]++R⟩ = some ⟨0,U++U++L,R⟩ := by cases d <;> rfl

theorem middle3D (d : Bool) (L R : List Bool) :
    run0 (p d 14) 5 ⟨0,[false]++L,[false,true,true]++R⟩ = some ⟨0,U++L,Y++R⟩ := by cases d <;> rfl

theorem middle3R (L : List Bool) :
    run0 (p true 15) 7 ⟨0,[false]++L,[false,true,true]⟩ = some ⟨0,U++U++L,[false]⟩ := by rfl

theorem evenB (d : Bool) (a : Nat) :
    run0 (p d 6) (4*a+9) (V a 0 U) = some (V 0 (a+1) [true]) := by
  have h := join0 (right d 6 a [false,true,true]) (middle3B d (rep U a) [])
  have w : U++U++rep U a = rep U (a+2)++[] := by simp only [rep,List.append_nil,List.append_assoc]
  rw [w] at h
  have g := join0 h (left d 6 (a+2) [] [])
  apply unpad d 6 _ _ _ (by omega)
  rw [even_out (a+1)] at g
  simpa only [V,show rep X 0=[] by rfl,List.nil_append,List.append_nil,List.append_assoc,U,List.cons_append,show 2*a+5+2*(a+2)=4*a+9 by omega] using g

theorem evenD (d : Bool) (a : Nat) :
    run0 (p d 14) (4*a+7) (V a 0 U) = some (V 0 (a+1) [true]) := by
  have h := join0 (right d 14 a [false,true,true]) (middle3D d (rep U a) [])
  have w : U++rep U a = rep U (a+1)++[] := by simp only [rep,List.append_nil]
  rw [w] at h
  have g := join0 h (left d 14 (a+1) [] Y)
  have ww : rep Y (a+1)++Y = rep Y (a+2) := by exact (rep_add Y (a+1) 1).symm
  apply unpad d 14 _ _ _ (by omega)
  rw [ww,even_out (a+1)] at g
  simpa only [V,show rep X 0=[] by rfl,List.nil_append,List.append_nil,List.append_assoc,U,List.cons_append,show 2*a+5+2*(a+1)=4*a+7 by omega] using g

theorem evenR (a : Nat) :
    run0 (p true 15) (4*a+11) (V a 0 U) = some (V 0 (a+2) []) := by
  have h := join0 (right true 15 a [false,true,true]) (middle3R (rep U a))
  have w : U++U++rep U a = rep U (a+2)++[] := by simp only [rep,List.append_nil,List.append_assoc]
  rw [w] at h
  have g := join0 h (left true 15 (a+2) [] [false])
  have ww : rep Y (a+2)++[false] = [false]++rep X (a+2) := by
    simpa using (rotate false [true] (a+2)).symm
  apply unpad true 15 _ _ _ (by omega)
  rw [ww] at g
  simpa only [V,show rep X 0=[] by rfl,List.nil_append,List.append_nil,List.append_assoc,U,List.cons_append,show 2*a+7+2*(a+2)=4*a+11 by omega] using g

theorem macro5Z (d : Bool) (v a : Nat) :
    run0 (p d v) (4*a+5) (V a 0 []) = some (V 0 a U) := by
  have mid (L : List Bool) : run0 (p d v) 3 ⟨0,[false]++L,[false]⟩ =
      some ⟨0,U++L,[true]⟩ := by cases d <;> rfl
  have h := join0 (right d v a [false]) (mid (rep U a))
  have w : U++rep U a = rep U (a+1)++[] := by simp only [rep,List.append_nil]
  rw [w] at h
  have g := join0 h (left d v (a+1) [] [true])
  apply unpad d v _ _ _ (by omega)
  rw [even_out a] at g
  simpa only [V,show rep X 0=[] by rfl,List.nil_append,List.append_nil,List.append_assoc,List.singleton_append,show 2*a+3+2*(a+1)=4*a+5 by omega] using g

theorem macro6Z (d : Bool) (v a : Nat) :
    run0 (p d v) (2*a+4) (V a 1 []) = some ⟨5,[false,false,true,true,true]++rep U a,[]⟩ := by
  have mid (L : List Bool) : run0 (p d v) 4 ⟨0,[false]++L,[false,true,false]⟩ =
      some ⟨5,[false,false,true,true,true]++L,[]⟩ := by cases d <;> rfl
  apply unpad d v _ _ _ (by omega)
  simpa only [V,rep,List.nil_append,List.append_nil,List.append_assoc,X,List.cons_append] using join0 (right d v a [false,true,false]) (mid (rep U a))

theorem entryB (d : Bool) : run0 (p d 6) (65+2*e d) (R0 []) = some (V 0 5 U) := by cases d <;> rfl
theorem entryD (d : Bool) : run0 (p d 14) (63+2*e d) (R0 []) = some (V 0 5 U) := by cases d <;> rfl
theorem entryR : run0 (p true 15) 71 (R0 []) = some (V 0 5 U) := by rfl

theorem traceBD (d vD : Bool) : run0 (p d (if vD then 14 else 6))
    ((if vD then 2649120 else 2649126)+1104*e d) (R0 []) =
      some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ := by
  let v := if vD then 14 else 6
  have en : run0 (p d v) ((if vD then 63 else 65)+2*e d) (R0 []) = some (V 0 5 U) := by
    cases vD
    · exact entryB d
    · exact entryD d
  have ev (a : Nat) : run0 (p d v) (4*a+(if vD then 7 else 9)) (V a 0 U) = some (V 0 (a+1) [true]) := by
    cases vD
    · exact evenB d a
    · exact evenD d a
  have h1 := join0 en (repeatAdvance d v 0 2 1 U)
  have h2 := join0 h1 (oddU d v 10)
  have h3 := join0 h2 (repeatAdvance d v 0 8 0 U)
  have h4 := join0 h3 (ev 40)
  have h5 := join0 h4 (repeatAdvance d v 0 20 1 [true])
  have h6 := join0 h5 (oddOne d v 100)
  have h7 := join0 h6 (repeatAdvance d v 0 52 1 U)
  have h8 := join0 h7 (oddU d v 260)
  have h9 := join0 h8 (repeatAdvance d v 0 133 0 U)
  have h10 := join0 h9 (ev 665)
  have h11 := join0 h10 (repeatAdvance d v 0 333 0 [true])
  have h12 := join0 h11 (macro6 d v 1665)
  cases d <;> cases vD <;> exact h12

theorem traceR : run0 (p true 15) 2651340 (R0 []) =
    some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ := by
  have h1 := join0 entryR (repeatAdvance true 15 0 2 1 U)
  have h2 := join0 h1 (oddU true 15 10)
  have h3 := join0 h2 (repeatAdvance true 15 0 8 0 U)
  have h4 := join0 h3 (evenR 40)
  have h5 := join0 h4 (repeatAdvance true 15 0 21 0 [])
  have h6 := join0 h5 (macro5Z true 15 105)
  have h7 := join0 h6 (repeatAdvance true 15 0 52 1 U)
  have h8 := join0 h7 (oddU true 15 260)
  have h9 := join0 h8 (repeatAdvance true 15 0 133 0 U)
  have h10 := join0 h9 (evenR 665)
  have h11 := join0 h10 (repeatAdvance true 15 0 333 1 [])
  have h12 := join0 h11 (macro6Z true 15 1665)
  exact h12

#print axioms traceBD
#print axioms traceR
end BB6.Agent46Raw13Coupled6LateCore
