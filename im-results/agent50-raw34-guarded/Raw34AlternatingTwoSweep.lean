import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34TwoSweep
open BB6Coverage BB6Coverage.Agent31Pump

/-!
The Raw34 D1=0LD C1=0LA depth-three holdout
  1RB0LB_1RC1RE_0RD0LA_1LC0LD_0RA---_------
admits an exact two-sweep unbounded growth recurrence.

At the nth left-frontier checkpoint the head is in B, its left tape
is empty, and its right tape is 001(01)^(2n)0 (including the zipper's explicit trailing zero). The nth epoch costs
28n+44 ordinary steps and increases the alternating marked block to
001(01)^(2n+2)0. This proves NeverHalts for EVERY total completion,
including completions in which E1,F0,F1 are HALT. The one-block sweep
lemmas quantify over arbitrary untouched left/right tails.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)  -- A0=1RB
  | 0,true  => some (some ⟨false,false,1⟩) -- A1=0LB
  | 1,false => some (some ⟨true,true,2⟩)  -- B0=1RC
  | 1,true  => some (some ⟨true,true,4⟩)  -- B1=1RE
  | 2,false => some (some ⟨false,true,3⟩) -- C0=0RD
  | 2,true  => some (some ⟨false,false,0⟩) -- C1=0LA
  | 3,false => some (some ⟨true,false,2⟩) -- D0=1LC
  | 3,true  => some (some ⟨false,false,3⟩) -- D1=0LD
  | 4,false => some (some ⟨false,true,0⟩) -- E0=0RA
  | _,_ => none

def P : List Bool := [false,true]
def family (n : Nat) : Z0 :=
  ⟨1, [], [false,false,true] ++ rep P (2*n) ++ [false]⟩

theorem first : run0 p 9 ⟨0,[],[]⟩ = some (family 0) := by decide

/-- Single finite source-exact bridge that creates the first left marker.
    The remainder R is opaque and can have arbitrary length. -/
theorem prepare (R : List Bool) :
    run0 p 11 ⟨1,[],[false,false,true]++R⟩ =
      some ⟨1,[true],[false,false,false,true]++R⟩ := by
  rfl

/-- Six source actions transport one 01 block rightward. -/
theorem right_one (L R : List Bool) :
    run0 p 6 ⟨1,[true]++L,[false,false]++P++R⟩ =
      some ⟨1,[true]++P++L,[false,false]++R⟩ := by
  rfl

/-- The blank right frontier has a four-step turn into C. -/
theorem right_frontier (L : List Bool) :
    run0 p 4 ⟨1,[true]++L,[false,false,false]⟩ =
      some ⟨2,[false,true,true,false,true]++L,[]⟩ := by
  rfl

/-- C/D's right-frontier turn enters B for the opposite sweep. -/
theorem left_turn (L : List Bool) :
    run0 p 7 ⟨2,[false,true,true,false,true]++L,[]⟩ =
      some ⟨1,P++L,[false,false,true,false]⟩ := by
  rfl

/-- Eight source actions transport one 01 block leftward. -/
theorem left_one (L R : List Bool) :
    run0 p 8 ⟨1,P++L,[false,false,true]++R⟩ =
      some ⟨1,L,[false,false,true]++P++R⟩ := by
  rfl

theorem growth (n : Nat) :
    run0 p (28*n+44) (family n) = some (family (n+1)) := by
  have h0 : run0 p 11 (family n) =
      some ⟨1,[true],[false,false]++rep P (2*n+1)++[false]⟩ := by
    have h := prepare (rep P (2*n)++[false])
    simpa [family, P, rep, List.append_assoc] using h
  have hR : run0 p (6*(2*n+1))
      ⟨1,[true],[false,false]++rep P (2*n+1)++[false]⟩ =
      some ⟨1,[true]++rep P (2*n+1),[false,false,false]⟩ := by
    have h := sweepR p 1 [true] [false,false] P P 6
      right_one (2*n+1) [] [false]
    simpa using h
  have hF : run0 p 4
      ⟨1,[true]++rep P (2*n+1),[false,false,false]⟩ =
      some ⟨2,[false,true,true,false,true]++rep P (2*n+1),[]⟩ :=
    right_frontier (rep P (2*n+1))
  have hT : run0 p 7
      ⟨2,[false,true,true,false,true]++rep P (2*n+1),[]⟩ =
      some ⟨1,rep P (2*n+2),[false,false,true,false]⟩ := by
    simpa [rep] using left_turn (rep P (2*n+1))
  have hL : run0 p (8*(2*n+2))
      ⟨1,rep P (2*n+2),[false,false,true,false]⟩ =
      some (family (n+1)) := by
    have h := sweepL p 1 [] [false,false,true] P P 8
      left_one (2*n+2) [] [false]
    have hsize : 2*(n+1) = 2*n+2 := by omega
    simpa [family,hsize,List.append_assoc] using h
  have h := join0 h0 (join0 hR (join0 hF (join0 hT hL)))
  have hc : 11+(6*(2*n+1)+(4+(7+8*(2*n+2)))) = 28*n+44 := by omega
  simpa only [hc] using h

/-- Every compatible completion has arbitrarily long ordinary runs. -/
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p family 9 (fun n => 28*n+44) first
  · intro n; omega
  · exact growth
  · exact hm

#print axioms first
#print axioms prepare
#print axioms right_one
#print axioms right_frontier
#print axioms left_turn
#print axioms left_one
#print axioms growth
#print axioms never
end BB6.Agent50Raw34TwoSweep
