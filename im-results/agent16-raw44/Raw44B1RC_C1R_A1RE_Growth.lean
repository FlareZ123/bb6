import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44B1RC_C1R_A1RE
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Raw44 B1=0RC, C1=1RA, A1=1RE, E1=0RF, F0=0RC, F1=0RE.
E0 is the only unspecified instruction.  Every compatible complete machine
has a growing blank-root return family; no guess about E0 is required.
The E/F-renamed sibling A1=1RF has an identical argument.
-/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 4,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true  => some (some ⟨false,true,4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n

/-- The head scans the leading one in B, the left tail has n zeros,
and the right tail contains precisely 2n+3 more ones. -/
def phase (n : Nat) : Z0 :=
  ⟨1,[true] ++ zeros n,ones (2*n+3)⟩

private theorem pairRep (b : Bool) (n : Nat) :
    rep [b,b] n = rep [b] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [b,b] (n+1) = [b,b] ++ rep [b,b] n := by rfl
      _ = [b,b] ++ rep [b] (2*n) := by rw [ih]
      _ = rep [b] (2*(n+1)) := by
        rw [show 2*(n+1)=2*n+2 by omega]
        rfl

private theorem ones3 (n : Nat) :
    ones (2*n+3) = [true,true,true] ++ ones (2*n) := by
  unfold ones
  rfl

private theorem zeros4 (n : Nat) :
    zeros (2*n+4) = [false,false,false,false] ++ zeros (2*n) := by
  unfold zeros
  rfl

private theorem zerosSucc (n : Nat) :
    zeros (n+1) = [false] ++ zeros n := by rfl

private theorem onesNext (n : Nat) :
    ones (2*(n+1)+3) = [true] ++ ones (2*n+4) := by
  rw [show 2*(n+1)+3 = (2*n+4)+1 by omega]
  rfl

/-- B1,C1,A1 advance through three ones, entering the E/F erasure sweep. -/
private theorem front (L R : List Bool) :
    run0 table 3 ⟨1,[true] ++ L,[true,true,true] ++ R⟩ =
      some ⟨4,[true,true,true,false] ++ L,R⟩ := by rfl

/-- Each E1,F1 pair erases two ones and returns to E. -/
private theorem epair (L R : List Bool) :
    run0 table 2 ⟨4,[true] ++ L,[true,true] ++ R⟩ =
      some ⟨4,[true,false,false] ++ L,R⟩ := by rfl

/-- On reaching the right blank, E1,F0,C0 enter D0. -/
private theorem efinish (L : List Bool) :
    run0 table 3 ⟨4,[true] ++ L,[]⟩ =
      some ⟨3,[false,false,false,false] ++ L,[]⟩ := by rfl

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false] ++ L,R⟩ =
      some ⟨3,L,[true] ++ R⟩ := by rfl

private theorem dfinish (L R : List Bool) :
    run0 table 1 ⟨3,[true,true,false] ++ L,R⟩ =
      some ⟨1,[true,false] ++ L,[true] ++ R⟩ := by rfl

/-- One full B-to-B phase takes exactly 4n+11 ordinary moves and adds
two consecutive ones to the right while moving the head one cell right. -/
theorem growth (n : Nat) :
    run0 table (4*n+11) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table 3 (phase n) =
      some ⟨4,[true,true,true,false] ++ zeros n,ones (2*n)⟩ := by
    simpa only [phase,ones3] using front (zeros n) (ones (2*n))
  have h2 : run0 table (2*n)
      ⟨4,[true,true,true,false] ++ zeros n,ones (2*n)⟩ =
      some ⟨4,[true] ++ zeros (2*n) ++ [true,true,false] ++ zeros n,[]⟩ := by
    have H := sweepR table 4 [true] [] [true,true] [false,false]
      2 epair n ([true,true,false] ++ zeros n) []
    simpa only [zeros,ones,pairRep,List.append_assoc,
      List.cons_append,List.append_nil,List.nil_append] using H
  have h3 : run0 table 3
      ⟨4,[true] ++ zeros (2*n) ++ [true,true,false] ++ zeros n,[]⟩ =
      some ⟨3,zeros (2*n+4) ++ [true,true,false] ++ zeros n,[]⟩ := by
    have H := efinish (zeros (2*n) ++ [true,true,false] ++ zeros n)
    simpa only [zeros4,List.append_assoc] using H
  have h4 : run0 table (2*n+4)
      ⟨3,zeros (2*n+4) ++ [true,true,false] ++ zeros n,[]⟩ =
      some ⟨3,[true,true,false] ++ zeros n,ones (2*n+4)⟩ := by
    have H := sweepL table 3 [] [] [false] [true]
      1 dstep (2*n+4) ([true,true,false] ++ zeros n) []
    simpa only [zeros,ones,Nat.one_mul,List.nil_append,
      List.append_nil,List.append_assoc] using H
  have h5 : run0 table 1
      ⟨3,[true,true,false] ++ zeros n,ones (2*n+4)⟩ =
      some (phase (n+1)) := by
    have H := dfinish (zeros n) (ones (2*n+4))
    simpa only [phase,zerosSucc,onesNext,List.cons_append,List.nil_append] using H
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((3+2*n)+3)+(2*n+4))+1 = 4*n+11 := by omega
  simpa only [ht] using H

/-- On the blank tape the first B phase occurs after exactly 6 moves. -/
theorem entry : run0 table 6 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 6 (fun n => 4*n+11) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44B1RC_C1R_A1RE
