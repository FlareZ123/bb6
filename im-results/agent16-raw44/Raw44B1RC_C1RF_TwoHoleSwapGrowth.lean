import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44B1RC_C1RF
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw44, B1=0RC, C1=0RF, E0=0RD, E1=1RD, F1=0RE.
    A1 and F0 remain undefined: 25^2 compatible complete tables.
    This is the E/F state-renaming of the certified C1=0RE two-hole growth table. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, true, 5⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, false, 1⟩)
  | 4, false => some (some ⟨false, true, 3⟩)
  | 4, true  => some (some ⟨true, true, 3⟩)
  | 5, true  => some (some ⟨false, true, 4⟩)
  | _, _ => none

def ones (n : Nat) : List Bool := rep [true] n
def zeros (n : Nat) : List Bool := rep [false] n
/-- B scans a blank with precisely 3n+2 ones to the right. -/
def core (n : Nat) : Z0 := ⟨1, [], ones (3*n+2)⟩
/-- The actual blank run reaches core 3 in 63 steps. -/
def phase (n : Nat) : Z0 := core (n+3)

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

private theorem onesSucc (n : Nat) :
    ones (n+1) = [true] ++ ones n := by rfl

private theorem zerosFour (n : Nat) :
    zeros (n+4) = [false,false,false,false] ++ zeros n := by
  rfl

private theorem onesNext (n : Nat) :
    ones (3*n+1) = rep [true,true,true] n ++ [true] := by
  rw [show 3*n+1=(3*n)+1 by omega,onesSucc]
  change [true] ++ rep [true] (3*n) = rep [true,true,true] n ++ [true]
  rw [← rep_snoc [true] (3*n), rep3 true n]

/-- The repeated five-step C1-E1-F1-D1-B1 packet consumes three 1s
    and moves the C1 head three cells to the right. -/
private theorem cpacket (L R : List Bool) :
    run0 table 5 ⟨2,[true]++L,[true,true,true]++R⟩ =
      some ⟨2,[true,false,false,false]++L,R⟩ := by rfl

/-- The terminal C1-E1-F0 packet reaches D0 on the fresh blank. -/
private theorem cfinish (L : List Bool) :
    run0 table 3 ⟨2,[true]++L,[true]⟩ =
      some ⟨3,[false,false,false,false]++L,[]⟩ := by rfl

/-- D0 writes 1 while retreating to the left. -/
private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl

/-- Uniform exact machine-level recursion. No A1/E0 query occurs. -/
theorem core_growth (n : Nat) :
    run0 table (8*n+9) (core n) = some (core (n+1)) := by
  have h1 : run0 table 1 (core n) =
      some ⟨2,[true,true],ones (3*n+1)⟩ := by
    have hs : ones (3*n+2) = [true] ++ ones (3*n+1) := by
      rw [show 3*n+2 = (3*n+1)+1 by omega]
      exact onesSucc (3*n+1)
    simpa only [core,hs,List.nil_append] using
      (show run0 table 1 ⟨1,[],[true]++ones (3*n+1)⟩ =
        some ⟨2,[true,true],ones (3*n+1)⟩ by rfl)
  have h2 : run0 table (5*n) ⟨2,[true,true],ones (3*n+1)⟩ =
      some ⟨2,[true]++zeros (3*n)++[true],[true]⟩ := by
    have H := sweepR table 2 [true] [] [true,true,true]
      [false,false,false] 5 cpacket n [true] [true]
    rw [onesNext n,zeros]
    rw [← rep3 false n]
    simpa only [List.nil_append,List.append_assoc,List.cons_append] using H
  have h3 : run0 table 3 ⟨2,[true]++zeros (3*n)++[true],[true]⟩ =
      some ⟨3,zeros (3*n+4)++[true],[]⟩ := by
    have H := cfinish (zeros (3*n)++[true])
    rw [zerosFour (3*n)]
    simpa only [List.append_assoc,List.cons_append] using H
  have h4 : run0 table (3*n+4) ⟨3,zeros (3*n+4)++[true],[]⟩ =
      some ⟨3,[true],ones (3*n+4)⟩ := by
    simpa only [ones,zeros,List.nil_append,List.append_nil,Nat.one_mul] using
      sweepL table 3 [] [] [false] [true] 1 dstep (3*n+4) [true] []
  have h5 : run0 table 1 ⟨3,[true],ones (3*n+4)⟩ =
      some (core (n+1)) := by
    have hs : ones (3*(n+1)+2) = [true]++ones (3*n+4) := by
      rw [show 3*(n+1)+2 = (3*n+4)+1 by omega]
      exact onesSucc (3*n+4)
    simpa only [core,hs] using
      (show run0 table 1 ⟨3,[true],ones (3*n+4)⟩ =
        some ⟨1,[],[true]++ones (3*n+4)⟩ by rfl)
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((1+5*n)+3)+(3*n+4))+1 = 8*n+9 := by omega
  simpa only [ht] using H

/-- Exact blank entry into phase 0. -/
theorem entry : run0 table 63 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- From the blank-entry family, the cost is 8n+33 per cycle. -/
theorem growth (n : Nat) :
    run0 table (8*n+33) (phase n) = some (phase (n+1)) := by
  change run0 table (8*n+33) (core (n+3)) =
    some (core ((n+1)+3))
  rw [show (n+1)+3=(n+3)+1 by omega]
  rw [show 8*n+33=8*(n+3)+9 by omega]
  exact core_growth (n+3)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 63 (fun n => 8*n+33) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms core_growth
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44B1RC_C1RF
