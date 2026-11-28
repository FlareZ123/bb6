import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44M3Swap
open BB6Coverage BB6Coverage.Agent31Pump

/-- E/F conjugate: B1=0RC C1=0LA, E0=1RA E1 undefined F0=0RB F1=0LE. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true  => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n
def phase (n : Nat) : Z0 := ⟨5,[true],[true,false]++ones (2*n+1)⟩

private theorem first9 (R : List Bool) :
    run0 table 9 ⟨5,[true],[true,false,true]++R⟩ =
      some ⟨5,[false,true,true],[true,false]++R⟩ := by rfl
private theorem packet7 (L R : List Bool) :
    run0 table 7 ⟨5,[false]++L,[true,false,true]++R⟩ =
      some ⟨5,[false,false]++L,[true,false]++R⟩ := by rfl
private theorem reset3 (L : List Bool) :
    run0 table 3 ⟨5,[false]++L,[true,false]⟩ =
      some ⟨3,[false,false,false,false]++L,[]⟩ := by rfl
private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl
private theorem reset7 (R : List Bool) :
    run0 table 7 ⟨3,[true,true],[true,true,true,true]++R⟩ =
      some ⟨5,[true],[true,false,true,true,true]++R⟩ := by rfl

private theorem onesSucc (n : Nat) :
    ones (n+1) = [true]++ones n := by rfl
private theorem onesFour (n : Nat) :
    ones (n+4) = [true,true,true,true]++ones n := by rfl
private theorem onesThree (n : Nat) :
    ones (n+3) = [true,true,true]++ones n := by rfl
private theorem zerosFour (n : Nat) :
    zeros (n+4) = [false,false,false,false]++zeros n := by rfl

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Exact blank-tape recurrence for the first of two E/F-conjugate residuals. -/
theorem growth (n : Nat) :
    run0 table (16*n+23) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table 9 (phase n) =
      some ⟨5,[false,true,true],[true,false]++ones (2*n)⟩ := by
    have hs : ones (2*n+1) = [true]++ones (2*n) := onesSucc (2*n)
    simpa only [phase,hs,List.append_assoc,List.cons_append,List.nil_append] using
      first9 (ones (2*n))
  have h2 : run0 table (7*(2*n))
      ⟨5,[false,true,true],[true,false]++ones (2*n)⟩ =
      some ⟨5,[false]++zeros (2*n)++[true,true],[true,false]⟩ := by
    simpa only [ones,zeros,List.nil_append,List.append_nil,Nat.one_mul,
       List.append_assoc,List.cons_append] using
      sweepR table 5 [false] [true,false] [true] [false] 7 packet7
        (2*n) [true,true] []
  have h3 : run0 table 3
      ⟨5,[false]++zeros (2*n)++[true,true],[true,false]⟩ =
      some ⟨3,zeros (2*n+4)++[true,true],[]⟩ := by
    have H := reset3 (zeros (2*n)++[true,true])
    have hz : zeros (2*n+4) = [false,false,false,false]++zeros (2*n) := zerosFour (2*n)
    simpa only [hz,List.append_assoc,List.cons_append,List.nil_append] using H
  have h4 : run0 table (2*n+4)
      ⟨3,zeros (2*n+4)++[true,true],[]⟩ =
      some ⟨3,[true,true],ones (2*n+4)⟩ := by
    simpa only [ones,zeros,List.nil_append,List.append_nil,Nat.one_mul] using
      sweepL table 3 [] [] [false] [true] 1 dstep (2*n+4) [true,true] []
  have h5 : run0 table 7
      ⟨3,[true,true],ones (2*n+4)⟩ =
      some (phase (n+1)) := by
    have H := reset7 (ones (2*n))
    have h4 : ones (2*n+4) = [true,true,true,true]++ones (2*n) := onesFour (2*n)
    have h3 : ones (2*(n+1)+1) = [true,true,true]++ones (2*n) := by
      rw [show 2*(n+1)+1=(2*n)+3 by omega]
      exact onesThree (2*n)
    simpa only [h4,phase,h3,List.append_assoc,List.cons_append,List.nil_append] using H
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((9+7*(2*n))+3)+(2*n+4))+7=16*n+23 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 12 (fun n => 16*n+23) entry
    (fun n => by omega) growth m hm
theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M3Swap
