import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44B1RC_C1R_A1ZeroRE
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Raw44 B1=0RC, C1=1RA, A1=0RE, E1=0RF, F0=0RD, F1=0RE.
E0 alone is unassigned.  The head returns to the same tape coordinate in B
with 2n+3 consecutive ones to its right and alternating scanned bit.
The E/F-renamed 0RF alternative follows by state symmetry.
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
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true  => some (some ⟨false,true,4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n

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
    ones (2*n+3) = [true,true,true] ++ ones (2*n) := by rfl

private theorem zeros4 (n : Nat) :
    zeros (2*n+4) = [false,false,false,false] ++ zeros (2*n) := by rfl

private theorem zerosMove (n : Nat) :
    [false,false,false] ++ zeros (2*n) ++ [false] = zeros (2*n+4) := by
  calc
    _ = [false,false,false] ++ ([false] ++ zeros (2*n)) := by
      rw [List.append_assoc]
      exact congrArg ([false,false,false] ++ ·) (rep_snoc [false] (2*n))
    _ = zeros (2*n+4) := by rw [zeros4]; rfl

private theorem onesIncrease (n : Nat) :
    ones (2*n+5) = [true] ++ ones (2*n+4) := by rfl

/-- The head at B carries bit b, which B flips while advancing to E. -/
private theorem front (b : Bool) (L R : List Bool) :
    run0 table 3 ⟨1,[b] ++ L,[true,true,true] ++ R⟩ =
      some ⟨4,[true,false,true,!b] ++ L,R⟩ := by
  cases b <;> rfl

private theorem epair (L R : List Bool) :
    run0 table 2 ⟨4,[true] ++ L,[true,true] ++ R⟩ =
      some ⟨4,[true,false,false] ++ L,R⟩ := by rfl

private theorem efinish (L : List Bool) :
    run0 table 2 ⟨4,[true] ++ L,[]⟩ =
      some ⟨3,[false,false,false] ++ L,[]⟩ := by rfl

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false] ++ L,R⟩ =
      some ⟨3,L,[true] ++ R⟩ := by rfl

private theorem dfinish (b : Bool) (R : List Bool) :
    run0 table 1 ⟨3,[true,b],R⟩ =
      some ⟨1,[b],[true] ++ R⟩ := by rfl

/-- Uniform one-phase law: 4n+10 moves, two fresh ones, and a flip of
the leftmost scanned bit.  The unspecified E0 is never consulted. -/
theorem stepPhase (b : Bool) (n : Nat) :
    run0 table (4*n+10) ⟨1,[b],ones (2*n+3)⟩ =
      some ⟨1,[!b],ones (2*n+5)⟩ := by
  have h1 : run0 table 3 ⟨1,[b],ones (2*n+3)⟩ =
      some ⟨4,[true,false,true,!b],ones (2*n)⟩ := by
    simpa only [ones3,List.append_nil] using front b [] (ones (2*n))
  have h2 : run0 table (2*n) ⟨4,[true,false,true,!b],ones (2*n)⟩ =
      some ⟨4,[true] ++ zeros (2*n) ++ [false,true,!b],[]⟩ := by
    have H := sweepR table 4 [true] [] [true,true] [false,false]
      2 epair n [false,true,!b] []
    simpa only [zeros,ones,pairRep,List.cons_append,List.append_assoc,
      List.append_nil,List.nil_append] using H
  have h3 : run0 table 2 ⟨4,[true] ++ zeros (2*n) ++ [false,true,!b],[]⟩ =
      some ⟨3,zeros (2*n+4) ++ [true,!b],[]⟩ := by
    have H := efinish (zeros (2*n) ++ [false,true,!b])
    rw [← zerosMove n]
    simpa only [List.cons_append,List.append_assoc,List.nil_append] using H
  have h4 : run0 table (2*n+4) ⟨3,zeros (2*n+4) ++ [true,!b],[]⟩ =
      some ⟨3,[true,!b],ones (2*n+4)⟩ := by
    have H := sweepL table 3 [] [] [false] [true]
      1 dstep (2*n+4) [true,!b] []
    simpa only [zeros,ones,Nat.one_mul,List.nil_append,
      List.append_nil,List.append_assoc] using H
  have h5 : run0 table 1 ⟨3,[true,!b],ones (2*n+4)⟩ =
      some ⟨1,[!b],ones (2*n+5)⟩ := by
    simpa only [onesIncrease] using dfinish (!b) (ones (2*n+4))
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((3+2*n)+2)+(2*n+4))+1 = 4*n+10 := by omega
  simpa only [ht] using H

def alternating : Nat → Bool
  | 0 => true
  | n+1 => !alternating n

def phase (n : Nat) : Z0 := ⟨1,[alternating n],ones (2*n+3)⟩

theorem growth (n : Nat) :
    run0 table (4*n+10) (phase n) = some (phase (n+1)) := by
  change run0 table (4*n+10) ⟨1,[alternating n],ones (2*n+3)⟩ =
    some ⟨1,[!alternating n],ones (2*(n+1)+3)⟩
  rw [show 2*(n+1)+3=2*n+5 by omega]
  exact stepPhase (alternating n) n

theorem entry : run0 table 6 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 6 (fun n => 4*n+10) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms stepPhase
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44B1RC_C1R_A1ZeroRE
