import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Raw44 B1=0RC, C1=1RA, A1=0RE, E1=0RF, F0=0RC, F1=0RA.
E0 is unassigned. The B phase visits the same tape coordinate with an
alternating scanned bit and an expanding run of ones on its right.
Every compatible completion is nonhalting.
-/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,false,1⟩)
  | 4,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n

private theorem rep3 (b : Bool) (n : Nat) :
    rep [b,b,b] n = rep [b] (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [b,b,b] (n+1) = [b,b,b] ++ rep [b,b,b] n := by rfl
      _ = [b,b,b] ++ rep [b] (3*n) := by rw [ih]
      _ = rep [b] (3*(n+1)) := by
        rw [show 3*(n+1)=3*n+3 by omega]
        rfl

private theorem ones2 (n : Nat) :
    ones (3*n+3) = [true,true] ++ ones (3*n+1) := by rfl

private theorem onesNext (n : Nat) :
    ones (3*n+1) = rep [true,true,true] n ++ [true] := by
  rw [show 3*n+1=(3*n)+1 by omega]
  change [true] ++ rep [true] (3*n) = rep [true,true,true] n ++ [true]
  rw [← rep_snoc [true] (3*n), rep3 true n]

private theorem zeros5 (n : Nat) :
    zeros (3*n+5) = [false,false,false,false,false] ++ zeros (3*n) := by rfl

private theorem onesIncrease (n : Nat) :
    ones (3*(n+1)+3) = [true] ++ ones (3*n+5) := by
  rw [show 3*(n+1)+3 = (3*n+5)+1 by omega]
  rfl

private theorem front (b : Bool) (L R : List Bool) :
    run0 table 2 ⟨1,[b] ++ L,[true,true] ++ R⟩ =
      some ⟨0,[true,true,!b] ++ L,R⟩ := by
  cases b <;> rfl

/-- A1,E1,F1 consume three ones, erase them and return to A. -/
private theorem apacket (L R : List Bool) :
    run0 table 3 ⟨0,[true] ++ L,[true,true,true] ++ R⟩ =
      some ⟨0,[true,false,false,false] ++ L,R⟩ := by rfl

/-- A1,E1,F0,C0 produce the fresh rightmost D0 blank. -/
private theorem afinish (L : List Bool) :
    run0 table 4 ⟨0,[true] ++ L,[true]⟩ =
      some ⟨3,[false,false,false,false,false] ++ L,[]⟩ := by rfl

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false] ++ L,R⟩ =
      some ⟨3,L,[true] ++ R⟩ := by rfl

private theorem dfinish (b : Bool) (R : List Bool) :
    run0 table 1 ⟨3,[true,b],R⟩ =
      some ⟨1,[b],[true] ++ R⟩ := by rfl

def alternating : Nat → Bool
  | 0 => true
  | n+1 => !alternating n

def phase (n : Nat) : Z0 := ⟨1,[alternating n],ones (3*n+3)⟩

/-- Uniform 6n+12-step primitive-machine phase recurrence. -/
theorem stepPhase (b : Bool) (n : Nat) :
    run0 table (6*n+12) ⟨1,[b],ones (3*n+3)⟩ =
      some ⟨1,[!b],ones (3*n+6)⟩ := by
  have h1 : run0 table 2 ⟨1,[b],ones (3*n+3)⟩ =
      some ⟨0,[true,true,!b],ones (3*n+1)⟩ := by
    simpa only [ones2,List.append_nil] using front b [] (ones (3*n+1))
  have h2 : run0 table (3*n) ⟨0,[true,true,!b],ones (3*n+1)⟩ =
      some ⟨0,[true] ++ zeros (3*n) ++ [true,!b],[true]⟩ := by
    have H := sweepR table 0 [true] [] [true,true,true] [false,false,false]
      3 apacket n [true,!b] [true]
    rw [onesNext n,zeros]
    rw [← rep3 false n]
    simpa only [List.append_assoc,List.cons_append,
      List.nil_append] using H
  have h3 : run0 table 4
      ⟨0,[true] ++ zeros (3*n) ++ [true,!b],[true]⟩ =
      some ⟨3,zeros (3*n+5) ++ [true,!b],[]⟩ := by
    have H := afinish (zeros (3*n) ++ [true,!b])
    rw [zeros5]
    simpa only [List.append_assoc,List.cons_append] using H
  have h4 : run0 table (3*n+5)
      ⟨3,zeros (3*n+5) ++ [true,!b],[]⟩ =
      some ⟨3,[true,!b],ones (3*n+5)⟩ := by
    have H := sweepL table 3 [] [] [false] [true]
      1 dstep (3*n+5) [true,!b] []
    simpa only [zeros,ones,Nat.one_mul,List.nil_append,
      List.append_nil,List.append_assoc] using H
  have h5 : run0 table 1 ⟨3,[true,!b],ones (3*n+5)⟩ =
      some ⟨1,[!b],ones (3*n+6)⟩ := by
    simpa only [show 3*n+6=(3*n+5)+1 by omega] using
      dfinish (!b) (ones (3*n+5))
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((2+3*n)+4)+(3*n+5))+1 = 6*n+12 := by omega
  simpa only [ht] using H

theorem growth (n : Nat) :
    run0 table (6*n+12) (phase n) = some (phase (n+1)) := by
  change run0 table (6*n+12) ⟨1,[alternating n],ones (3*n+3)⟩ =
    some ⟨1,[!alternating n],ones (3*(n+1)+3)⟩
  rw [show 3*(n+1)+3=3*n+6 by omega]
  exact stepPhase (alternating n) n

theorem entry : run0 table 6 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 6 (fun n => 6*n+12) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms stepPhase
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44C1RA_A1ZeroRE_F0RC
