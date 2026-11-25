import SweepPumping
namespace BB6.Agent10Raw108RF62
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev Q := [true,true]
abbrev H := [false,true,true,true,true]
abbrev I := [true,true,true,true,true]
abbrev Z := [false,false,false,false,true]
abbrev O := [false,false,true,true,true]
abbrev M := [false,true]
abbrev P := [false,true,true,true]
abbrev S := [true,false,false,false,false,true]

theorem entryFirst (R : List Bool) :
    run0 table 5 ⟨0,[],S++R⟩ = some ⟨2,P++M,true::R⟩ := by rfl
theorem entrySweep (L R : List Bool) :
    run0 table 8 ⟨2,P++L,[true]++Q++R⟩ = some ⟨2,P++Q++L,[true]++R⟩ := by rfl
theorem entryLast (L R : List Bool) :
    run0 table 5 ⟨2,P++L,[true,false,false]++R⟩ = some ⟨1,I++L,[false,false]++R⟩ := by rfl
theorem entryRaw (n : Nat) (R : List Bool) :
    run0 table (10+8*n) ⟨0,[],S++rep Q n++[false,false]++R⟩ =
      some ⟨1,I++rep Q n++M,[false,false]++R⟩ := by
  have h1 := entryFirst (rep Q n++[false,false]++R)
  have h2 := sweepR table 2 P [true] Q Q 8 entrySweep n M ([false,false]++R)
  have h3 := entryLast (rep Q n++M) R
  have h1' : run0 table 5 ⟨0,[],S++rep Q n++[false,false]++R⟩ =
      some ⟨2,P++M,[true]++rep Q n++([false,false]++R)⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h1
  have h3' : run0 table 5 ⟨2,P++rep Q n++M,[true]++([false,false]++R)⟩ =
      some ⟨1,I++rep Q n++M,[false,false]++R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h3
  have H := join0 (join0 h1' h2) h3'
  simpa only [show 5+8*n+5=10+8*n by omega] using H

theorem onesCommute (n : Nat) : I++rep Q n=rep Q n++I := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,← List.append_assoc]
    rw [show I++Q=Q++I by rfl,List.append_assoc,ih,← List.append_assoc]

theorem finishSweep (L R : List Bool) :
    run0 table 2 ⟨0,Q++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
theorem finishLast (R : List Bool) :
    run0 table 16 ⟨0,I++M,R⟩ = some ⟨0,[],[true,false,false,false,false,true,true,true]++R⟩ := by rfl
theorem finishRaw (n : Nat) (R : List Bool) :
    run0 table (16+2*n) ⟨0,I++rep Q n++M,R⟩ =
      some ⟨0,[],[true,false,false,false,false,true,true,true]++rep Q n++R⟩ := by
  have h := sweepL table 0 [] [] Q Q 2 finishSweep n (I++M) R
  have H := join0 (by simpa only [List.nil_append] using h) (finishLast (rep Q n++R))
  rw [← List.append_assoc,← onesCommute] at H
  simpa only [List.append_assoc,show 2*n+16=16+2*n by omega] using H

def enc : List Bool → List Bool
  | [] => Z
  | false::bs => Z++enc bs
  | true::bs => O++enc bs

def stack (n j : Nat) := I++rep H j++rep Q n++M

inductive Section
  | start : Nat → List Bool → Section
  | carry : Nat → Nat → List Bool → Section
  | drain : Nat → Nat → List Bool → Section

def sectionCfg : Section → Z0
  | .start n bs => ⟨0,[],S++rep Q n++enc bs⟩
  | .carry n j bs => ⟨1,stack n j,enc bs⟩
  | .drain n j bs => ⟨0,stack n j,enc bs⟩

def next : Section → Section
  | .start n bs => .carry n 0 bs
  | .carry n j [] => .drain n (j+1) []
  | .carry n j (false::bs) => .carry n (j+1) bs
  | .carry n j (true::bs) => .drain n j (false::bs)
  | .drain n 0 bs => .start (n+1) bs
  | .drain n (j+1) bs => .drain n j (true::bs)

def cost : Section → Nat
  | .start n _ => 10+8*n
  | .carry _ _ [] => 27
  | .carry _ _ (false::_) => 9
  | .carry _ _ (true::_) => 12
  | .drain n 0 _ => 16+2*n
  | .drain _ (_+1) _ => 9

theorem carryZero (L R : List Bool) :
    run0 table 9 ⟨1,I++L,Z++[false,false]++R⟩ =
      some ⟨1,I++H++L,[false,false]++R⟩ := by rfl
theorem carryOne (L R : List Bool) :
    run0 table 12 ⟨1,I++L,O++R⟩ = some ⟨0,I++L,Z++R⟩ := by rfl
theorem carryEnd (L : List Bool) :
    run0 table 27 ⟨1,I++L,Z⟩ = some ⟨0,I++H++L,Z⟩ := by rfl
theorem drainOne (L R : List Bool) :
    run0 table 9 ⟨0,I++H++L,R⟩ = some ⟨0,I++L,O++R⟩ := by rfl

theorem encPrefix (bs : List Bool) : ∃ R, enc bs = [false,false]++R := by
  cases bs with
  | nil => exact ⟨[false,false,true],rfl⟩
  | cons b bs =>
    cases b
    · exact ⟨[false,false,true]++enc bs,rfl⟩
    · exact ⟨[true,true,true]++enc bs,rfl⟩

theorem advance (s : Section) : run0 table (cost s) (sectionCfg s) = some (sectionCfg (next s)) := by
  cases s with
  | start n bs =>
    obtain ⟨R,hR⟩ := encPrefix bs
    simp only [cost,sectionCfg,next,stack,rep,List.append_nil,hR]
    simpa only [List.append_assoc] using entryRaw n R
  | carry n j bs =>
    cases bs with
    | nil =>
      simpa only [cost,next,sectionCfg,stack,enc,rep,List.append_assoc] using carryEnd (rep H j++rep Q n++M)
    | cons b bs =>
      cases b
      · obtain ⟨R,hR⟩ := encPrefix bs
        simp only [cost,next,sectionCfg,stack,enc,rep,hR]
        simpa only [List.append_assoc] using carryZero (rep H j++rep Q n++M) R
      · simpa only [cost,next,sectionCfg,stack,enc,List.append_assoc] using carryOne (rep H j++rep Q n++M) (enc bs)
  | drain n j bs =>
    cases j with
    | zero =>
      simpa only [cost,next,sectionCfg,stack,rep,List.nil_append,List.append_nil,List.append_assoc,S,I,Q,M,List.cons_append] using finishRaw n (enc bs)
    | succ j =>
      simpa only [cost,next,sectionCfg,stack,enc,rep,List.append_assoc] using drainOne (rep H j++rep Q n++M) (enc bs)

theorem positive (s : Section) : 0 < cost s := by
  cases s with
  | start n bs => simp [cost]; omega
  | carry n j bs => cases bs with
    | nil => simp [cost]
    | cons b bs => cases b <;> simp [cost]
  | drain n j bs => cases j <;> simp [cost] <;> omega

def orbit : Nat → Section
  | 0 => .start 0 []
  | n+1 => next (orbit n)
def family (n : Nat) := sectionCfg (orbit n)
theorem entry : run0 table 47 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := advance (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 47 (fun n => cost (orbit n)) entry (fun n => positive (orbit n)) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108RF62
