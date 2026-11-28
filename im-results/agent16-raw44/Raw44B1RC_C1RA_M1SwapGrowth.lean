import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44M1Swap
open BB6Coverage BB6Coverage.Agent31Pump

/-- E/F conjugate Raw44 B1=0RC C1=0RA; A1=0LF, E0=1LA, E1=1LB, F0=0LE, F1 unspecified. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def U : List Bool := [false,true,true,false,false]
def Blk : List Bool := [false,false,true,true,true]

/-- Exact eleven-step packet transport 00111 ↦ 01100. -/
private theorem packet11 (L R : List Bool) :
  run0 table 11 ⟨5,[false,true,true]++L,[false,true]++Blk++R⟩ =
  some ⟨5,[false,true,true]++U++L,[false,true]++R⟩ := by rfl

/-- Exact fixed middle reset, valid for arbitrary left suffix. -/
private theorem startup31 (L : List Bool) :
  run0 table 31 ⟨5,[false,true,true]++L,[false,true]⟩ =
  some ⟨5,[false,false]++L,[false,true]++Blk⟩ := by rfl

/-- Exact fifteen-step 01100 ↦ 00111 back-packet. -/
private theorem packet15 (L R : List Bool) :
  run0 table 15 ⟨5,[false,false]++U++L,[false,true]++R⟩ =
  some ⟨5,[false,false]++L,[false,true]++Blk++R⟩ := by rfl

def rightSeq (n : Nat) : List Bool := [false,true]++rep Blk n

/-- Generalized 26n+31 pump, valid for any fixed left base word. -/
private theorem drain (n : Nat) (base : List Bool) :
  run0 table (26*n+31) ⟨5,[false,true,true]++base,rightSeq n⟩ =
    some ⟨5,[false,false]++base,rightSeq (n+1)⟩ := by
  have h1 : run0 table (11*n)
      ⟨5,[false,true,true]++base,rightSeq n⟩ =
      some ⟨5,[false,true,true]++rep U n++base,[false,true]⟩ := by
    simpa only [rightSeq,List.append_assoc,List.nil_append,List.append_nil] using
      sweepR table 5 [false,true,true] [false,true] Blk U 11 packet11 n base []
  have h2 : run0 table 31
      ⟨5,[false,true,true]++rep U n++base,[false,true]⟩ =
      some ⟨5,[false,false]++rep U n++base,[false,true]++Blk⟩ := by
    simpa only [List.append_assoc] using startup31 (rep U n++base)
  have h3 : run0 table (15*n)
      ⟨5,[false,false]++rep U n++base,[false,true]++Blk⟩ =
      some ⟨5,[false,false]++base,rightSeq (n+1)⟩ := by
    have H := sweepL table 5 [false,false] [false,true] U Blk 15
      packet15 n base Blk
    have hs : rep Blk n++Blk=rep Blk (n+1) := by
      rw [rep_snoc]
      rfl
    simpa only [rightSeq,hs,List.append_assoc,List.append_nil] using H
  have H := join0 (join0 h1 h2) h3
  have ht : (11*n+31)+(15*n) = 26*n+31 := by omega
  simpa only [ht] using H

private theorem transformA40 (R : List Bool) :
  run0 table 40 ⟨5,[false,false,false,true],[false,true]++Blk++R⟩ =
    some ⟨5,[false,true,true,false,false,false,true],[false,true]++Blk++R⟩ := by rfl
private theorem transformAend20 (R : List Bool) :
  run0 table 20 ⟨5,[false,false,false,false,false,true],[false,true]++Blk++R⟩ =
    some ⟨5,[false,true,true,false,true,true],[false,true]++Blk++R⟩ := by rfl
private theorem transformB35 (R : List Bool) :
  run0 table 35 ⟨5,[false,false,false,true,true],[false,true]++Blk++R⟩ =
    some ⟨5,[false,true,true,false,true],[false,true]++Blk++Blk++R⟩ := by rfl

def A (n : Nat) : Z0 := ⟨5,[false,true,true,false,true],rightSeq n⟩
def B (n : Nat) : Z0 := ⟨5,[false,true,true,false,true,true],rightSeq n⟩

/-- Exact transition between the two distinct growing return sections. -/
theorem A_to_B (n : Nat) :
    run0 table (52*n+148) (A n) = some (B (n+2)) := by
  have h1 : run0 table (26*n+31) (A n) =
      some ⟨5,[false,false,false,true],rightSeq (n+1)⟩ := by
    simpa only [A,List.cons_append,List.nil_append,List.append_assoc] using
      drain n [false,true]
  have h2 : run0 table 40 ⟨5,[false,false,false,true],rightSeq (n+1)⟩ =
      some ⟨5,[false,true,true,false,false,false,true],rightSeq (n+1)⟩ := by
    simpa only [rightSeq,rep,List.append_assoc,List.cons_append,List.nil_append] using
      transformA40 (rep Blk n)
  have h3 : run0 table (26*(n+1)+31)
      ⟨5,[false,true,true,false,false,false,true],rightSeq (n+1)⟩ =
      some ⟨5,[false,false,false,false,false,true],rightSeq (n+2)⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using
      drain (n+1) [false,false,false,true]
  have h4 : run0 table 20
      ⟨5,[false,false,false,false,false,true],rightSeq (n+2)⟩ =
      some (B (n+2)) := by
    simpa only [B,rightSeq,rep,List.append_assoc,List.cons_append,List.nil_append] using
      transformAend20 (rep Blk (n+1))
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : (((26*n+31)+40)+(26*(n+1)+31))+20=52*n+148 := by omega
  simpa only [ht] using H

theorem B_to_A (n : Nat) :
    run0 table (26*n+66) (B n) = some (A (n+2)) := by
  have h1 : run0 table (26*n+31) (B n) =
      some ⟨5,[false,false,false,true,true],rightSeq (n+1)⟩ := by
    simpa only [B,List.cons_append,List.nil_append,List.append_assoc] using
      drain n [false,true,true]
  have h2 : run0 table 35
      ⟨5,[false,false,false,true,true],rightSeq (n+1)⟩ =
      some (A (n+2)) := by
    simpa only [A,rightSeq,rep,List.append_assoc,List.cons_append,List.nil_append] using
      transformB35 (rep Blk n)
  have H := join0 h1 h2
  have ht : (26*n+31)+35=26*n+66 := by omega
  simpa only [ht] using H

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (A 0) := by rfl

/-- Advance A(4n) to A(4n+4) via B(4n+2) in 312n+266 steps. -/
def phase (n : Nat) : Z0 := A (4*n)

theorem growth (n : Nat) :
    run0 table (312*n+266) (phase n) = some (phase (n+1)) := by
  have h1 := A_to_B (4*n)
  have h2 := B_to_A (4*n+2)
  have H := join0 h1 h2
  have ht : (52*(4*n)+148)+(26*(4*n+2)+66)=312*n+266 := by omega
  simpa only [phase,show 4*(n+1)=(4*n+2)+2 by omega,ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 29 (fun n => 312*n+266) entry
    (fun n => by omega) growth m hm
theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms A_to_B
#print axioms B_to_A
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent16Raw44M1Swap
