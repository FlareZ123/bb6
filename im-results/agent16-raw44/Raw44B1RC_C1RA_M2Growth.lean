import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44M2
open BB6Coverage BB6Coverage.Agent31Pump

/-- Raw44 B1=0RC C1=0RA, A1=1RE, E1=0RF, F0=0RC, F1=0RE; E0 undefined. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n
/-- The blank execution enters this canonical literal section in 9 steps. -/
def phase (n : Nat) : Z0 :=
  ⟨4,[true,true,false]++ones n++[false],ones (2*n)⟩

private theorem epair (L R : List Bool) :
    run0 table 2 ⟨4,[true]++L,[true,true]++R⟩ =
      some ⟨4,[true,false,false]++L,R⟩ := by rfl
private theorem prefix3 (L : List Bool) :
    run0 table 3 ⟨4,[true]++L,[]⟩ =
      some ⟨3,[false,false,false,false]++L,[]⟩ := by rfl
private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl
private theorem finish4 (L R : List Bool) :
    run0 table 4 ⟨3,[true,false]++L,[true,true,true,true]++R⟩ =
      some ⟨4,[true,true,false,true]++L,[true,true]++R⟩ := by rfl
private theorem pair (b : Bool) (n : Nat) :
    rep [b,b] n = rep [b] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [b,b] (n+1) = [b,b]++rep [b,b] n := by rfl
      _ = [b,b]++rep [b] (2*n) := by rw [ih]
      _ = rep [b] (2*(n+1)) := by
        rw [show 2*(n+1)=2*n+2 by omega]
        rfl
private theorem onesTwo (n : Nat) :
    ones (n+2) = [true,true]++ones n := by rfl
private theorem onesFour (n : Nat) :
    ones (n+4) = [true,true,true,true]++ones n := by rfl
private theorem zerosFour (n : Nat) :
    zeros (n+4) = [false,false,false,false]++zeros n := by rfl
private theorem onesSucc (n : Nat) :
    ones (n+1) = [true]++ones n := by rfl

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Exact 4n+11 growing return, with literal blank entry, for all n. -/
theorem growth (n : Nat) :
    run0 table (4*n+11) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table (2*n) (phase n) =
      some ⟨4,[true]++zeros (2*n)++[true,false]++ones n++[false],[]⟩ := by
    have H := sweepR table 4 [true] [] [true,true] [false,false]
      2 epair n ([true,false]++ones n++[false]) []
    have hp : rep [true,true] n = ones (2*n) := pair true n
    have hz : rep [false,false] n = zeros (2*n) := pair false n
    simpa only [phase,hp,hz,ones,zeros,List.append_assoc,
      List.nil_append,List.append_nil,List.cons_append] using H
  have h2 : run0 table 3
      ⟨4,[true]++zeros (2*n)++[true,false]++ones n++[false],[]⟩ =
      some ⟨3,zeros (2*n+4)++[true,false]++ones n++[false],[]⟩ := by
    have H := prefix3 (zeros (2*n)++[true,false]++ones n++[false])
    have hz : zeros (2*n+4) = [false,false,false,false]++zeros (2*n) := zerosFour (2*n)
    simpa only [hz,List.append_assoc,List.cons_append,List.nil_append] using H
  have h3 : run0 table (2*n+4)
      ⟨3,zeros (2*n+4)++[true,false]++ones n++[false],[]⟩ =
      some ⟨3,[true,false]++ones n++[false],ones (2*n+4)⟩ := by
    simpa only [ones,zeros,List.nil_append,List.append_nil,Nat.one_mul,List.append_assoc] using
      sweepL table 3 [] [] [false] [true] 1 dstep (2*n+4)
        ([true,false]++ones n++[false]) []
  have h4 : run0 table 4
      ⟨3,[true,false]++ones n++[false],ones (2*n+4)⟩ =
      some (phase (n+1)) := by
    have H := finish4 (ones n++[false]) (ones (2*n))
    have hr : ones (2*n+4) = [true,true,true,true]++ones (2*n) := onesFour (2*n)
    have hn : ones (n+1) = [true]++ones n := onesSucc n
    have hrr : ones (2*(n+1)) = [true,true]++ones (2*n) := by
      rw [show 2*(n+1)=(2*n)+2 by omega]
      exact onesTwo (2*n)
    simpa only [phase,hr,hn,hrr,List.append_assoc,List.cons_append,List.nil_append] using H
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((2*n+3)+(2*n+4))+4 = 4*n+11 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 9 (fun n => 4*n+11) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M2
