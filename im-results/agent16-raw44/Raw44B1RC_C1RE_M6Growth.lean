import SweepPumping
set_option maxRecDepth 15000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44M6
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw44 with B1=0RC C1=0RE and sole F0 hole:
    1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0RE. -/
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
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 :=
  ⟨4,[false],rep [true,false] (2*n+1) ++ [true]⟩

private theorem start4 (R : List Bool) :
  run0 table 4 ⟨4,[false],[true,false]++R⟩ =
  some ⟨4,[false,false,true,true],R⟩ := by rfl

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

private theorem backward4 (L R : List Bool) :
  run0 table 4 ⟨4,[false,true,true]++L,[true]++R⟩ =
  some ⟨4,[false]++L,[true,false,true]++R⟩ := by rfl

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
    [false,false,true,true]++rep [true,true] (2*n)++[true,true] =
    [false,false]++ones (4*n+4) := by
  have hs := rep_snoc [true,true] (2*n)
  rw [List.append_assoc, hs, pair]
  rw [show 4*n+4=(2*(2*n))+4 by omega,onesFour]
  rfl

private theorem resetWords (n : Nat) :
    [false,false]++ones (4*n+4) =
    [false,false,true,true,true,true]++ones (4*n) := by
  rw [show 4*n+4=(4*n)+4 by omega,onesFour]
  rfl

private theorem resetWords2 (n : Nat) :
    [false,false]++ones (4*n+4) =
    [false,false,true,true]++ones (4*n+2) := by
  rw [show 4*n+4=(4*n+2)+2 by omega,onesTwo]
  rfl

private theorem resetWords3 (n : Nat) :
    [false,true,true,true,true]++ones (4*n+2) =
    [false]++ones (4*n+6) := by
  rw [show 4*n+6=(4*n+2)+4 by omega,onesFour]
  rfl

/-- The right sweep consumes every 10 token and converts it to 11. -/
theorem forward (n : Nat) :
    run0 table (8*n+8) (phase n) =
      some ⟨4,[false,false]++ones (4*n+4),[]⟩ := by
  have h1 : run0 table 4 (phase n) =
      some ⟨4,[false,false,true,true],rep [true,false] (2*n)++[true]⟩ := by
    simpa only [phase,rep,List.append_assoc,List.nil_append,List.cons_append] using
      start4 (rep [true,false] (2*n)++[true])
  have h2 : run0 table (4*(2*n))
      ⟨4,[false,false,true,true],rep [true,false] (2*n)++[true]⟩ =
      some ⟨4,[false,false]++rep [true,true] (2*n)++[true,true],[true]⟩ := by
    have H := sweepR table 4 [false,false] [] [true,false]
       [true,true] 4 forward4 (2*n) [true,true] [true]
    simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H
  have h3 : run0 table 4
      ⟨4,[false,false]++rep [true,true] (2*n)++[true,true],[true]⟩ =
      some ⟨4,[false,false]++ones (4*n+4),[]⟩ := by
    have H := end4 (rep [true,true] (2*n)++[true,true])
    simpa only [←forwardWords n,List.append_assoc,List.cons_append,List.nil_append] using H
  have H := join0 (join0 h1 h2) h3
  have ht : 4+4*(2*n)+4 = 8*n+8 := by omega
  simpa only [ht] using H

/-- Fixed reset and exact packet rotation return to a longer right tape. -/
theorem backward (n : Nat) :
    run0 table (8*n+27) ⟨4,[false,false]++ones (4*n+4),[]⟩ =
      some (phase (n+1)) := by
  have h1 : run0 table 10 ⟨4,[false,false]++ones (4*n+4),[]⟩ =
      some ⟨4,[false,false]++ones (4*n+4),[true,true]⟩ := by
    have H := reset10 (ones (4*n))
    simpa only [resetWords n,List.append_assoc,List.nil_append,List.cons_append] using H
  have h2 : run0 table 5 ⟨4,[false,false]++ones (4*n+4),[true,true]⟩ =
      some ⟨4,[false]++ones (4*n+6),[true]⟩ := by
    have H := reset5 (ones (4*n+2))
    simpa only [resetWords2 n,resetWords3 n,List.append_assoc,List.nil_append,List.cons_append] using H
  have h3 : run0 table (4*(2*n+3))
      ⟨4,[false]++ones (4*n+6),[true]⟩ =
      some (phase (n+1)) := by
    have H := sweepL table 4 [false] [true] [true,true]
       [false,true] 4 backward4 (2*n+3) [] []
    have hp : ones (4*n+6) = rep [true,true] (2*n+3) := by
      rw [pair]
      congr 1
      omega
    have hr : [true] ++ rep [false,true] (2*n+3) =
        rep [true,false] (2*n+3) ++ [true] := by
      induction (2*n+3) with
      | zero => rfl
      | succ k ih =>
        calc
          [true]++rep [false,true] (k+1) =
              [true,false]++([true]++rep [false,true] k) := by rfl
          _ = [true,false]++(rep [true,false] k++[true]) := by rw [ih]
          _ = rep [true,false] (k+1)++[true] := by rfl
    simpa only [phase,show 2*(n+1)+1=2*n+3 by omega,hp,
        ←hr,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H
  have H := join0 (join0 h1 h2) h3
  have ht : 10+5+4*(2*n+3) = 8*n+27 := by omega
  simpa only [ht] using H

/-- Genuine blank-tape entry, not a prepared-state hypothesis. -/
theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- The exact recurrence adds two 10 packets, costing 16n+35 raw moves. -/
theorem growth (n : Nat) :
    run0 table (16*n+35) (phase n) = some (phase (n+1)) := by
  have H := join0 (forward n) (backward n)
  have ht : (8*n+8)+(8*n+27)=16*n+35 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 18 (fun n => 16*n+35) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms forward
#print axioms backward
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M6
