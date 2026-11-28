import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34LeftUnaryShellRD
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
A second new four-hole Raw34 nonhalting unary-shell candidate:
  1RB---_1RC---_0RD1LC_1LC1RF_------_1RD1RF
F0=1RD (not 1LC): an extra D0=1LC turn creates TWO new marks
per F checkpoint. The exact left-zipper invariant is
  0 1^(n+1) 011
with a blank head and empty right zipper; n -> n+2 has duration
2n+8. Every completion of A1,B1,E0,E1, including HALT, diverges.
All-time theorem uses the original infinite-tape soundness bridge.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true  => some (some ⟨true,true,5⟩)
  | _,_ => none

def word (n : Nat) : Z0 :=
  ⟨5,[false,true]++rep [true] n++[false,true,true],[]⟩

theorem first : run0 p 6 ⟨0,[],[]⟩ = some (word 0) := by decide

theorem fToD (n : Nat) :
    run0 p 1 (word n) =
    some ⟨3,[false,true,true]++rep [true] n++[false,true,true],[]⟩ := by rfl

theorem dToC (n : Nat) :
    run0 p 1
      ⟨3,[false,true,true]++rep [true] n++[false,true,true],[]⟩ =
    some ⟨2,[true,true]++rep [true] n++[false,true,true],[true]⟩ := by
  rfl

theorem cLeftOne (L R : List Bool) :
    run0 p 1 ⟨2,[true]++L,R⟩ =
      some ⟨2,L,[true]++R⟩ := by rfl

theorem cLeftMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨2,rep [true] n++L,R⟩ =
      some ⟨2,L,rep [true] n++R⟩ := by
  have h := sweepL p 2 [] [] [true] [true] 1
    cLeftOne n L R
  simpa only [List.nil_append,Nat.one_mul] using h

theorem turn (R : List Bool) :
    run0 p 2 ⟨2,[false,true,true],[true,true]++R⟩ =
      some ⟨5,[true,true,false,true,true],R⟩ := by rfl

theorem fRightOne (L R : List Bool) :
    run0 p 1 ⟨5,[true]++L,[true]++R⟩ =
      some ⟨5,[true,true]++L,R⟩ := by rfl

theorem fRightMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨5,[true]++L,rep [true] n++R⟩ =
      some ⟨5,[true]++rep [true] n++L,R⟩ := by
  have h := sweepR p 5 [true] [] [true] [true] 1
    fRightOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem fFinish (L : List Bool) :
    run0 p 1 ⟨5,[true]++L,[]⟩ =
      some ⟨5,[false,true]++L,[]⟩ := by rfl

theorem grow (n : Nat) :
    run0 p (2*n+8) (word n) =
      some (word (n+2)) := by
  have h1 := fToD n
  have h2 := dToC n
  have h3 := cLeftMany (n+2) [false,true,true] [true]
  have h4 := turn (rep [true] (n+1))
  have h5 := fRightMany (n+1) [true,false,true,true] []
  have h6 := fFinish (rep [true] (n+1)++[true,false,true,true])
  have h3' : run0 p (n+2)
      ⟨2,[true,true]++rep [true] n++[false,true,true],[true]⟩ =
      some ⟨2,[false,true,true],[true,true]++rep [true] (n+1)⟩ := by
    simpa [rep,rep_snoc,List.cons_append,List.nil_append,List.append_assoc] using h3
  have h5' : run0 p (n+1)
      ⟨5,[true,true,false,true,true],rep [true] (n+1)⟩ =
      some ⟨5,[true]++rep [true] (n+1)++[true,false,true,true],[]⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h5
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3') h4) h5') h6
  have ht : 1+1+(n+2)+2+(n+1)+1=2*n+8 := by omega
  simpa [word,rep,rep_snoc,List.cons_append,List.nil_append,List.append_assoc,ht] using H

def family (k : Nat) : Z0 := word (2*k)
def cost (k : Nat) : Nat := 4*k+8

theorem familyFirst :
    run0 p 6 ⟨0,[],[]⟩ = some (family 0) := by
  simpa only [family,Nat.zero_mul] using first

theorem familyGrowth (k : Nat) :
    run0 p (cost k) (family k) =
      some (family (k+1)) := by
  have h := grow (2*k)
  simpa only [family,cost,show 2*(2*k)+8=4*k+8 by omega,
    show 2*k+2=2*(k+1) by omega] using h

theorem all_time_never (m : Machine)
    (hm : compatible p m) : NeverHalts m := by
  exact never_of_growth p family 6 cost familyFirst
    (by intro k; unfold cost; omega) familyGrowth m hm

#print axioms first
#print axioms cLeftMany
#print axioms turn
#print axioms fRightMany
#print axioms grow
#print axioms familyGrowth
#print axioms all_time_never
end BB6.Agent40Raw34LeftUnaryShellRD
