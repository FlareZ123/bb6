import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RD1M0
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw43RD1Growth (rep_double)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def Q : List Bool := [true,false]
def X : List Bool := Q++Q
def H : List Bool := [false,false,false,true]
def endL : List Bool := [false,false,true]
def markR : List Bool := [true,false,false]

def sect (n : Nat) : Z0 := ⟨0,[],[false,false]++rep Q (2*(n+1))⟩
def mid (n r : Nat) : Z0 :=
  ⟨4,[true]++rep H n++endL,rep Q (r+2)⟩

private theorem entryOne (R : List Bool) :
    run0 table 13 ⟨0,[],[false,false]++X++R⟩ =
      some ⟨4,[true]++endL,markR++R⟩ := by rfl
private theorem rightOne (L R : List Bool) :
    run0 table 14 ⟨4,[true]++L,markR++X++R⟩ =
      some ⟨4,[true]++H++L,markR++R⟩ := by rfl
private theorem rightEnd (L : List Bool) :
    run0 table 8 ⟨4,[true]++L,markR⟩ =
      some ⟨4,[true]++H++L,[]⟩ := by rfl
private theorem firstLeft (L : List Bool) :
    run0 table 10 ⟨4,[true]++H++L,[]⟩ =
      some ⟨4,[true]++L,rep Q 3⟩ := by rfl
private theorem midOne (L R : List Bool) :
    run0 table 22 ⟨4,[true]++H++L,X++R⟩ =
      some ⟨4,[true]++L,rep Q 4++R⟩ := by rfl
private theorem midEnd (R : List Bool) :
    run0 table 22 ⟨4,[true]++endL,X++R⟩ =
      some ⟨0,[],[false,false]++rep Q 3++R⟩ := by rfl

theorem midSweep (n r : Nat) :
    run0 table (22*n) (mid n r) = some (mid 0 (r+2*n)) := by
  induction n generalizing r with
  | zero => simp [mid,run0]
  | succ n ih =>
    have h1 := midOne (rep H n++endL) (rep Q r)
    have h1' : run0 table 22 (mid (n+1) r) = some (mid n (r+2)) := by
      simpa only [mid,rep,X,List.append_assoc] using h1
    have h2 := ih (r+2)
    have h := join0 h1' h2
    rw [show 22+22*n=22*(n+1) by omega,
      show r+2+2*n=r+2*(n+1) by omega] at h
    exact h

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (sect 0) := by rfl

theorem epoch (n : Nat) :
    run0 table (36*(n+1)+17) (sect n) = some (sect (n+1)) := by
  have h0 : run0 table 13 (sect n) =
      some ⟨4,[true]++endL,markR++rep X n⟩ := by
    unfold sect
    rw [rep_double]
    simpa only [rep,X,List.append_assoc] using entryOne (rep X n)
  have hs := sweepR table 4 [true] markR X H 14 rightOne n endL []
  have hs' : run0 table (14*n) ⟨4,[true]++endL,markR++rep X n⟩ =
      some ⟨4,[true]++rep H n++endL,markR⟩ := by
    simpa only [List.append_nil] using hs
  have h2 := rightEnd (rep H n++endL)
  have h3 := firstLeft (rep H n++endL)
  have h23 : run0 table (8+10) ⟨4,[true]++rep H n++endL,markR⟩ =
      some (mid n 1) := by
    simpa only [mid,List.append_assoc] using join0 h2 h3
  have h4 := midSweep n 1
  have h5 : run0 table 22 (mid 0 (1+2*n)) = some (sect (n+1)) := by
    have h := midEnd (rep Q (1+2*n))
    rw [show 2*(n+1+1)=1+2*n+3 by omega]
    simpa only [mid,sect,rep,X,List.nil_append,List.append_assoc] using h
  have h := join0 (join0 (join0 (join0 h0 hs') h23) h4) h5
  rw [show 13+14*n+(8+10)+22*n+22=36*(n+1)+17 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 17 (fun n => 36*(n+1)+17) entry
    (by intro n; omega) epoch m hm

#print axioms epoch
#print axioms never
end BB6.Agent25Raw43RD1M0
