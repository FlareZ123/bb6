import SweepPumping
set_option maxRecDepth 15000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44M5
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw44 with B1=0RC C1=0RE and F0 the only hole:
    1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0LA. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 :=
  ⟨4,[false,false,true,true],rep [true,false] (2*n+2) ++ [true]⟩

private theorem forward4 (L R : List Bool) :
  run0 table 4 ⟨4,[false,false]++L,[true,false]++R⟩ =
  some ⟨4,[false,false,true,true]++L,R⟩ := by rfl

private theorem end4 (L : List Bool) :
  run0 table 4 ⟨4,[false,false]++L,[true]⟩ =
  some ⟨4,[false,false,true,true]++L,[]⟩ := by rfl

private theorem reset10 (L : List Bool) :
  run0 table 10 ⟨4,[false,false,true,true,true,true]++L,[]⟩ =
  some ⟨4,[false,false,true,true,true,true]++L,[true,true]⟩ := by rfl

private theorem reset5 (L : List Bool) :
  run0 table 5 ⟨4,[false,false,true,true]++L,[true,true]⟩ =
  some ⟨4,[false,true,true,true,true]++L,[true]⟩ := by rfl

private theorem astep (L R : List Bool) :
  run0 table 2 ⟨0,[true,true]++L,R⟩ =
    some ⟨0,L,[false,true]++R⟩ := by rfl

private theorem finish3 (R : List Bool) :
  run0 table 3 ⟨0,[],[false,true,false]++R⟩ =
    some ⟨4,[false,false,true,true],R⟩ := by rfl

private theorem pair (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true] (n+1) = [true,true]++rep [true,true] n := by rfl
      _ = [true,true]++ones (2*n) := by rw [ih]
      _ = ones (2*(n+1)) := by
        rw [show 2*(n+1)=(2*n)+2 by omega]
        rfl

private theorem onesFour (n : Nat) :
    ones (n+4) = [true,true,true,true]++ones n := by rfl

private theorem onesTwo (n : Nat) :
    ones (n+2) = [true,true]++ones n := by rfl

private theorem forwardWords (n : Nat) :
    [false,false,true,true]++rep [true,true] (2*n+2)++[true,true] =
    [false,false]++ones (4*n+8) := by
  have hs := rep_snoc [true,true] (2*n+2)
  rw [List.append_assoc, hs, pair]
  rw [show 4*n+8=(2*(2*n+2))+4 by omega,onesFour]
  rfl

private theorem resetWords (n : Nat) :
    [false,false]++ones (4*n+8) =
    [false,false,true,true,true,true]++ones (4*n+4) := by
  rw [show 4*n+8=(4*n+4)+4 by omega,onesFour]
  rfl

private theorem resetWords2 (n : Nat) :
    [false,false]++ones (4*n+8) =
    [false,false,true,true]++ones (4*n+6) := by
  rw [show 4*n+8=(4*n+6)+2 by omega,onesTwo]
  rfl

private theorem resetWords3 (n : Nat) :
    [false,true,true,true,true]++ones (4*n+6) =
    [false]++ones (4*n+10) := by
  rw [show 4*n+10=(4*n+6)+4 by omega,onesFour]
  rfl

private theorem rotatePairs (k : Nat) :
    [true]++rep [false,true] k = rep [true,false] k ++ [true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      [true]++rep [false,true] (k+1) =
          [true,false]++([true]++rep [false,true] k) := by rfl
      _ = [true,false]++(rep [true,false] k++[true]) := by rw [ih]
      _ = rep [true,false] (k+1)++[true] := by rfl

private theorem finishingWords (k : Nat) :
    rep [false,true] (k+2) =
    [false,true,false]++rep [true,false] k++[true] := by
  calc
    rep [false,true] (k+2) =
        [false,true,false]++([true]++rep [false,true] k) := by rfl
    _ = [false,true,false]++(rep [true,false] k++[true]) := by rw [rotatePairs k]
    _ = [false,true,false]++rep [true,false] k++[true] := by rfl

/-- Exact 8n+12 rightward packet conversion to a unary band. -/
theorem forward (n : Nat) :
    run0 table (8*n+12) (phase n) =
      some ⟨4,[false,false]++ones (4*n+8),[]⟩ := by
  have h1 : run0 table (4*(2*n+2)) (phase n) =
      some ⟨4,[false,false]++rep [true,true] (2*n+2)++[true,true],[true]⟩ := by
    have H := sweepR table 4 [false,false] [] [true,false]
       [true,true] 4 forward4 (2*n+2) [true,true] [true]
    simpa only [phase,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H
  have h2 : run0 table 4
      ⟨4,[false,false]++rep [true,true] (2*n+2)++[true,true],[true]⟩ =
      some ⟨4,[false,false]++ones (4*n+8),[]⟩ := by
    have H := end4 (rep [true,true] (2*n+2)++[true,true])
    simpa only [←forwardWords n,List.append_assoc,List.cons_append,List.nil_append] using H
  have H := join0 h1 h2
  have ht : 4*(2*n+2)+4=8*n+12 := by omega
  simpa only [ht] using H

/-- Reset, then exact leftward A1/F1 sweep and three-step terminal packet. -/
theorem backward (n : Nat) :
    run0 table (4*n+29) ⟨4,[false,false]++ones (4*n+8),[]⟩ =
      some (phase (n+1)) := by
  have h1 : run0 table 10 ⟨4,[false,false]++ones (4*n+8),[]⟩ =
      some ⟨4,[false,false]++ones (4*n+8),[true,true]⟩ := by
    have H := reset10 (ones (4*n+4))
    simpa only [resetWords n,List.append_assoc,List.nil_append,List.cons_append] using H
  have h2 : run0 table 5 ⟨4,[false,false]++ones (4*n+8),[true,true]⟩ =
      some ⟨4,[false]++ones (4*n+10),[true]⟩ := by
    have H := reset5 (ones (4*n+6))
    simpa only [resetWords2 n,resetWords3 n,List.append_assoc,List.nil_append,List.cons_append] using H
  have h3 : run0 table 1 ⟨4,[false]++ones (4*n+10),[true]⟩ =
      some ⟨0,ones (4*n+10),[false,true]⟩ := by rfl
  have h4 : run0 table (2*(2*n+5))
      ⟨0,ones (4*n+10),[false,true]⟩ =
      some ⟨0,[],rep [false,true] (2*n+6)⟩ := by
    have H := sweepL table 0 [] [] [true,true]
      [false,true] 2 astep (2*n+5) [] [false,true]
    have hp : ones (4*n+10) = rep [true,true] (2*n+5) := by
      rw [pair]
      congr 1
      omega
    have hr : rep [false,true] (2*n+5)++[false,true] =
        rep [false,true] (2*n+6) := by
      rw [rep_snoc]
      rfl
    simpa only [hp, ←hr, List.append_assoc,List.nil_append,List.append_nil] using H
  have h5 : run0 table 3 ⟨0,[],rep [false,true] (2*n+6)⟩ =
      some (phase (n+1)) := by
    have H := finish3 (rep [true,false] (2*n+4)++[true])
    have hs : rep [false,true] (2*n+6) =
        [false,true,false]++rep [true,false] (2*n+4)++[true] := by
      rw [show 2*n+6=(2*n+4)+2 by omega]
      exact finishingWords (2*n+4)
    simpa only [phase,show 2*(n+1)+2=2*n+4 by omega,hs,
       List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : 10+5+1+2*(2*n+5)+3=4*n+29 := by omega
  simpa only [ht] using H

theorem entry : run0 table 49 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem growth (n : Nat) :
    run0 table (12*n+41) (phase n) = some (phase (n+1)) := by
  have H := join0 (forward n) (backward n)
  have ht : (8*n+12)+(4*n+29)=12*n+41 := by omega
  simpa only [ht] using H

/-- All 25 completions of the unused F0 row never halt. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 49 (fun n => 12*n+41) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms forward
#print axioms backward
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M5
