import SweepPumping
set_option maxRecDepth 15000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44M4
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw44 B1=0RC C1=0RE; F1 is the only remaining hole in this
    concrete E0=1LF E1=1LC F0=1LA cylinder. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 := ⟨4,[],[false]++ones (4*n+4)⟩

private theorem front (R : List Bool) :
  run0 table 5 ⟨4,[],[false]++R⟩ =
  some ⟨4,[false,false,false,true],R⟩ := by rfl

private theorem startup (R : List Bool) :
  run0 table 5 ⟨4,[false,false,false,true],[true]++R⟩ =
  some ⟨4,[true,false,false,true,true],R⟩ := by rfl

private theorem epacket (L R : List Bool) :
  run0 table 5 ⟨4,[true,false]++L,[true]++R⟩ =
  some ⟨4,[true,false,true]++L,R⟩ := by rfl

private theorem efinish (L : List Bool) :
  run0 table 5 ⟨4,[true,false]++L,[]⟩ =
  some ⟨4,[false,false,true]++L,[]⟩ := by rfl

private theorem backpair (L R : List Bool) :
  run0 table 10 ⟨4,[false,false,true,true]++[true,true]++L,R⟩ =
  some ⟨4,[false,false,true,true]++L,[true,true]++R⟩ := by rfl

private theorem special (R : List Bool) :
  run0 table 8 ⟨4,[false,false,true,true,false,true,true],R⟩ =
  some ⟨4,[false,false,true,true,true],[true,true]++R⟩ := by rfl

private theorem tail10 (R : List Bool) :
  run0 table 10 ⟨4,[false,false,true,true,true],R⟩ =
  some ⟨4,[false,false,true],[true,true]++R⟩ := by rfl

private theorem tail3 (R : List Bool) :
  run0 table 3 ⟨4,[false,false,true],R⟩ =
  some ⟨4,[],[false,true,true]++R⟩ := by rfl

private theorem onesSucc (n : Nat) :
    ones (n+1) = [true] ++ ones n := by rfl

private theorem pair (n : Nat) :
    rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true] (n+1) = [true,true]++rep [true,true] n := by rfl
      _ = [true,true]++ones (2*n) := by rw [ih]
      _ = ones (2*(n+1)) := by
        rw [show 2*(n+1)=(2*n)+2 by omega]
        rfl

private theorem leftNext (n : Nat) :
    [false,false]++ones (4*n+4)++[false,true,true] =
    [false,false,true,true]++rep [true,true] (2*n+1)++[false,true,true] := by
  rw [pair]
  have hm : 2*(2*n+1) = 4*n+2 := by omega
  rw [hm]
  rw [show 4*n+4=(4*n+2)+2 by omega]
  rfl

private theorem rightNext (n : Nat) :
    [false,true,true]++[true,true]++[true,true]++ones (4*n+2) =
      [false]++ones (4*(n+1)+4) := by
  rw [show 4*(n+1)+4=(4*n+2)+6 by omega]
  rfl

/-- Exact growing rightward sweep from the authentic E0 section. -/
theorem forward (n : Nat) :
    run0 table (20*n+30) (phase n) =
      some ⟨4,[false,false]++ones (4*n+4)++[false,true,true],[]⟩ := by
  have h1 : run0 table 5 (phase n) =
      some ⟨4,[false,false,false,true],ones (4*n+4)⟩ := by
    simpa only [phase] using front (ones (4*n+4))
  have h2 : run0 table 5 ⟨4,[false,false,false,true],ones (4*n+4)⟩ =
      some ⟨4,[true,false,false,true,true],ones (4*n+3)⟩ := by
    have hs : ones (4*n+4) = [true]++ones (4*n+3) := by
      rw [show 4*n+4=(4*n+3)+1 by omega]
      exact onesSucc (4*n+3)
    simpa only [hs] using startup (ones (4*n+3))
  have h3 : run0 table (5*(4*n+3))
      ⟨4,[true,false,false,true,true],ones (4*n+3)⟩ =
      some ⟨4,[true,false]++ones (4*n+3)++[false,true,true],[]⟩ := by
    have H := sweepR table 4 [true,false] [] [true] [true]
      5 epacket (4*n+3) [false,true,true] []
    simpa only [ones,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H
  have h4 : run0 table 5
      ⟨4,[true,false]++ones (4*n+3)++[false,true,true],[]⟩ =
      some ⟨4,[false,false]++ones (4*n+4)++[false,true,true],[]⟩ := by
    have H := efinish (ones (4*n+3)++[false,true,true])
    have hs : ones (4*n+4) = [true]++ones (4*n+3) := by
      rw [show 4*n+4=(4*n+3)+1 by omega]
      exact onesSucc (4*n+3)
    simpa only [hs,List.append_assoc,List.cons_append,List.nil_append] using H
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : 5+5+5*(4*n+3)+5 = 20*n+30 := by omega
  simpa only [ht] using H

/-- Exact return sweep; the fixed three-stage reset does not touch F1. -/
theorem backward (n : Nat) :
    run0 table (20*n+31)
      ⟨4,[false,false]++ones (4*n+4)++[false,true,true],[]⟩ =
      some (phase (n+1)) := by
  have h1 : run0 table (10*(2*n+1))
      ⟨4,[false,false]++ones (4*n+4)++[false,true,true],[]⟩ =
      some ⟨4,[false,false,true,true,false,true,true],ones (4*n+2)⟩ := by
    have H := sweepL table 4 [false,false,true,true] [] [true,true]
      [true,true] 10 backpair (2*n+1) [false,true,true] []
    rw [leftNext n]
    have hp : rep [true,true] (2*n+1) = ones (4*n+2) := by
      rw [pair]
      congr 1
      omega
    simpa only [hp,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H
  have h2 : run0 table 8
      ⟨4,[false,false,true,true,false,true,true],ones (4*n+2)⟩ =
      some ⟨4,[false,false,true,true,true],[true,true]++ones (4*n+2)⟩ :=
    special (ones (4*n+2))
  have h3 : run0 table 10
      ⟨4,[false,false,true,true,true],[true,true]++ones (4*n+2)⟩ =
      some ⟨4,[false,false,true],[true,true]++[true,true]++ones (4*n+2)⟩ :=
    tail10 ([true,true]++ones (4*n+2))
  have h4 : run0 table 3
      ⟨4,[false,false,true],[true,true]++[true,true]++ones (4*n+2)⟩ =
      some (phase (n+1)) := by
    have H := tail3 ([true,true]++[true,true]++ones (4*n+2))
    have hr := rightNext n
    simpa only [phase, ← hr, List.append_assoc, List.nil_append] using H
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((10*(2*n+1)+8)+10)+3 = 20*n+31 := by omega
  simpa only [ht] using H

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem growth (n : Nat) :
    run0 table (40*n+61) (phase n) = some (phase (n+1)) := by
  have H := join0 (forward n) (backward n)
  have ht : (20*n+30)+(20*n+31)=40*n+61 := by omega
  simpa only [ht] using H

/-- All 25 F1 completions are nonhalting from the original blank tape. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 29 (fun n => 40*n+61) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms forward
#print axioms backward
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M4
