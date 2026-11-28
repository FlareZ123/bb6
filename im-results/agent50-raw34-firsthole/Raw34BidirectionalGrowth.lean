import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Bidirectional
open BB6Coverage BB6Coverage.Agent31Pump

/-!
A genuinely two-sided growing Raw34 child:
  1RB---_1RC1LB_0RD1RC_1LC1LA_------_------
Once A0 is queried the head is one zero to the left of a marked cell.
B1=1LB sweeps left across a growing solid marked interval until it meets
a fresh zero; B0 adds one marked cell and returns right to C; C1=1RC
sweeps to the right edge; the four-step C0,D0,C0,D1 turnaround adds one
marked cell at the new right edge and returns to A at a fresh zero.

After the n-th turnaround A scans a blank between 3n+2 marked cells on
its left and exactly one marked cell on its right. The next turnaround
takes 6n+14 steps and grows the contiguous left block by 3.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,false,0⟩)
  | _,_ => none

def bits (k : Nat) : List Bool := rep [true] k

def familyK (k : Nat) : Z0 :=
  ⟨0,[false]++bits k,[true]⟩

def family (n : Nat) : Z0 := familyK (3*n+2)

theorem first : run0 p 6 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem left_one :
    ∀ L R, run0 p 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by
  intro L R
  rfl

theorem right_one :
    ∀ L R, run0 p 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,true]++L,R⟩ := by
  intro L R
  rfl

theorem shift_true (k : Nat) :
    [true]++bits k = bits k++[true] := by
  change bits (k+1) = bits k++[true]
  exact rep_snoc [true] k

theorem bits_three (k : Nat) :
    [true]++bits k++[true,true] = bits (k+3) := by
  have h1 : bits (k+1) = bits k++[true] :=
    rep_snoc [true] k
  have h2 : bits (k+2) = bits (k+1)++[true] := by
    simpa [Nat.add_assoc] using (rep_snoc [true] (k+1))
  have h3 : bits (k+3) = bits (k+2)++[true] := by
    simpa [Nat.add_assoc] using (rep_snoc [true] (k+2))
  rw [h3,h2,h1]
  rw [shift_true]
  simp [List.append_assoc]

theorem growK (k : Nat) :
    run0 p (2*k+10) (familyK k) = some (familyK (k+3)) := by
  have hA : run0 p 1 (familyK k) =
      some ⟨1,[true,true]++bits k,[]⟩ := by
    rfl
  have hB2 : run0 p 2 ⟨1,[true,true]++bits k,[]⟩ =
      some ⟨1,bits k,[true,true]⟩ := by
    rfl
  have hBk : run0 p k ⟨1,bits k,[true,true]⟩ =
      some ⟨1,[],[true,true]++bits k⟩ := by
    have h := sweepL p 1 [] [true,true] [true] [true] 1
      left_one k [] []
    simpa [bits] using h
  have hB0 : run0 p 1 ⟨1,[],[true,true]++bits k⟩ =
      some ⟨2,[true,true],[true]++bits k⟩ := by
    rfl
  have hC1 : run0 p 1 ⟨2,[true,true],[true]++bits k⟩ =
      some ⟨2,[true,true,true],bits k⟩ := by
    rfl
  have hCk : run0 p k ⟨2,[true,true,true],bits k⟩ =
      some ⟨2,[true]++bits k++[true,true],[]⟩ := by
    have h := sweepR p 2 [true] [] [true] [true] 1
      right_one k [true,true] []
    simpa [bits] using h
  have hEnd : run0 p 5
      ⟨2,[true]++bits k++[true,true],[]⟩ =
      some (familyK (k+3)) := by
    have hraw : run0 p 5
        ⟨2,[true]++bits k++[true,true],[]⟩ =
        some ⟨0,[false]++([true]++bits k++[true,true]),[true]⟩ := by
      rfl
    simpa [familyK,bits_three] using hraw
  have h := join0 hA (join0 hB2 (join0 hBk
    (join0 hB0 (join0 hC1 (join0 hCk hEnd)))))
  have hc : 1+(2+(k+(1+(1+(k+5))))) = 2*k+10 := by omega
  simpa only [hc] using h

theorem growth (n : Nat) :
    run0 p (6*n+14) (family n) = some (family (n+1)) := by
  have h := growK (3*n+2)
  have hc : 2*(3*n+2)+10 = 6*n+14 := by omega
  have hn : (3*n+2)+3 = 3*(n+1)+2 := by omega
  simpa [family,hc,hn] using h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p family 6 (fun n => 6*n+14) first
  · intro n; omega
  · exact growth
  · exact hm

#print axioms first
#print axioms left_one
#print axioms right_one
#print axioms shift_true
#print axioms bits_three
#print axioms growK
#print axioms growth
#print axioms never
end BB6.Agent50Raw34Bidirectional
