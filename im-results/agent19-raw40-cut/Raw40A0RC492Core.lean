import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0RC492
open BB6Coverage BB6Coverage.Agent31Pump

/-- Canonical Raw40 A1=0RC, C1=0LE leaf 492. E1 is free. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

abbrev U (n : Nat) : List Bool := List.replicate n true
abbrev Z (n : Nat) : List Bool := List.replicate n false

theorem uAdd (a b : Nat) : U (a+b) = U a++U b := List.replicate_append_replicate.symm
theorem zAdd (a b : Nat) : Z (a+b) = Z a++Z b := List.replicate_append_replicate.symm
theorem uSucc (a : Nat) : U (a+1) = true::U a := List.replicate_succ
theorem zSucc (a : Nat) : Z (a+1) = false::Z a := List.replicate_succ


theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]

theorem rep_pair (b : Bool) (n : Nat) : rep [b,b] n = List.replicate (2*n) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,ih]
    change List.replicate 2 b ++ List.replicate (2*n) b = _
    rw [List.replicate_append_replicate]
    congr 1 <;> omega

/-- Pair erase within a nonempty run of ones, preserving both arbitrary tails. -/
theorem pair (L R : List Bool) : run0 table 2 ⟨1,[true]++L,[true,true]++R⟩ =
    some ⟨1,[true]++[false,false]++L,R⟩ := by rfl

theorem beginOdd (L R : List Bool) : run0 table 1 ⟨0,false::L,true::R⟩ =
    some ⟨1,true::true::L,R⟩ := by rfl

theorem eraseOdd (a : Nat) (L R : List Bool) :
    run0 table (1+2*a) ⟨0,false::L,U (2*a+1)++R⟩ =
    some ⟨1,true::(Z (2*a)++true::L),R⟩ := by
  have h1 := beginOdd L (U (2*a)++R)
  have h2 := sweepR table 1 [true] [] [true,true] [false,false] 2 pair a (true::L) R
  simp only [rep_pair,List.nil_append,List.singleton_append] at h2
  have H := join0 h1 h2
  rw [uSucc]
  simpa only [List.cons_append] using H

theorem dMove (L R : List Bool) : run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem dEnd (L R : List Bool) : run0 table 1 ⟨3,true::L,R⟩ = some ⟨0,L,true::R⟩ := by rfl

theorem dSweep (n : Nat) (L R : List Bool) :
    run0 table (n+1) ⟨3,Z n++true::L,R⟩ = some ⟨0,L,true::(U n++R)⟩ := by
  have h := sweepL table 3 [] [] [false] [true] 1 dMove n (true::L) R
  simp only [rep_single,List.nil_append,Nat.one_mul] at h
  exact join0 h (dEnd L (U n++R))

/-- Three zeros beyond the odd run: grow the run by four and move left one cell. -/
theorem oddTurn (L R : List Bool) : run0 table 3 ⟨1,true::L,[false,false,false]++R⟩ =
    some ⟨3,[false,false,false,false]++L,R⟩ := by rfl

theorem oddEpoch (a : Nat) (L R : List Bool) :
    run0 table (4*a+9) ⟨0,false::L,U (2*a+1)++Z 3++R⟩ =
    some ⟨0,L,U (2*a+5)++R⟩ := by
  have h1 := eraseOdd a L (Z 3++R)
  have h2 := oddTurn (Z (2*a)++true::L) R
  have h3 := dSweep (2*a+4) L R
  have h2' : run0 table 3 ⟨1,true::(Z (2*a)++true::L),Z 3++R⟩ =
      some ⟨3,Z (2*a+4)++true::L,R⟩ := by
    rw [show 2*a+4=4+2*a by omega,zAdd 4 (2*a)]
    simpa only [List.append_assoc,show Z 3=[false,false,false] by rfl,show Z 4=[false,false,false,false] by rfl] using h2
  have H := join0 (join0 h1 h2') h3
  rw [show 1+2*a+3+(2*a+4+1)=4*a+9 by omega] at H
  rw [show 2*a+5=(2*a+4)+1 by omega,uSucc (2*a+4)]
  simpa only [List.append_assoc,List.singleton_append,List.cons_append] using H

/-- A run of k odd growth epochs; closed cost, no primitive simulation. -/
theorem oddMany (a k : Nat) (L R : List Bool) :
    run0 table (k*(4*a+4*k+5)) ⟨0,Z k++L,U (2*a+1)++Z (3*k)++R⟩ =
    some ⟨0,L,U (2*a+1+4*k)++R⟩ := by
  induction k generalizing a with
  | zero => simp [run0]
  | succ k ih =>
    have h1 := oddEpoch a (Z k++L) (Z (3*k)++R)
    have h2 := ih (a+2)
    have h2' : run0 table (k*(4*(a+2)+4*k+5)) ⟨0,Z k++L,U (2*a+5)++(Z (3*k)++R)⟩ =
        some ⟨0,L,U (2*(a+2)+1+4*k)++R⟩ := by
      simpa only [List.append_assoc,show 2*(a+2)+1=2*a+5 by omega] using h2
    have h := join0 h1 h2' 
    have hc : 4*a+9+k*(4*(a+2)+4*k+5) = (k+1)*(4*a+4*(k+1)+5) := by
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_succ,Nat.one_mul]
      omega
    rw [hc] at h
    rw [show 3*(k+1)=3+3*k by omega,zAdd 3 (3*k)]
    rw [zSucc]
    have hu : 2*(a+2)+1+4*k=2*a+1+4*(k+1) := by omega
    rw [hu] at h
    simpa only [List.append_assoc,List.cons_append] using h

/-- A1 with another one immediately right; consume the right one and move left. -/
theorem leftOne (L R : List Bool) : run0 table 3 ⟨0,[true]++L,[true]++R⟩ =
    some ⟨0,L,[true]++[false]++R⟩ := by rfl

theorem leftMany (k : Nat) (L R : List Bool) :
    run0 table (3*k) ⟨0,U k++L,true::R⟩ = some ⟨0,L,true::(Z k++R)⟩ := by
  simpa only [rep_single,List.nil_append,List.singleton_append,List.append_assoc,List.cons_append] using
    sweepL table 0 [] [true] [true] [false] 3 leftOne k L R

/-- Move a singleton marker across a run, transferring its ones to the left. -/
theorem transferOne (L R : List Bool) : run0 table 5 ⟨0,[false]++L,[true,false]++[true]++R⟩ =
    some ⟨0,[false]++[true]++L,[true,false]++R⟩ := by rfl

theorem transferMany (k : Nat) (L R : List Bool) :
    run0 table (5*k) ⟨0,false::L,[true,false]++U k++R⟩ =
    some ⟨0,false::(U k++L),[true,false]++R⟩ := by
  simpa only [rep_single,List.nil_append,List.singleton_append,List.append_assoc,List.cons_append] using
    sweepR table 0 [false] [true,false] [true] [true] 5 transferOne k L R

/-- One zero and then a one after an odd run. -/
theorem oddOneTurn (L R : List Bool) : run0 table 4 ⟨1,true::L,[false,true]++R⟩ =
    some ⟨0,false::L,[true,false]++R⟩ := by rfl

theorem oddOne (a : Nat) (L R : List Bool) :
    run0 table (2*a+5) ⟨0,false::L,U (2*a+1)++[false,true]++R⟩ =
    some ⟨0,Z (2*a+1)++true::L,[true,false]++R⟩ := by
  have h := join0 (eraseOdd a L ([false,true]++R)) (oddOneTurn (Z (2*a)++true::L) R)
  rw [show 1+2*a+4=2*a+5 by omega] at h
  rw [zSucc]
  simpa only [List.append_assoc,List.cons_append] using h

/-- Two zeros then a one after the odd run: D turns immediately. -/
theorem oddTwoTurn (L R : List Bool) : run0 table 4 ⟨1,true::L,[false,false,true]++R⟩ =
    some ⟨0,[false,false,false]++L,true::R⟩ := by rfl

theorem oddTwo (a : Nat) (L R : List Bool) :
    run0 table (2*a+5) ⟨0,false::L,U (2*a+1)++[false,false,true]++R⟩ =
    some ⟨0,Z (2*a+3)++true::L,true::R⟩ := by
  have h := join0 (eraseOdd a L ([false,false,true]++R)) (oddTwoTurn (Z (2*a)++true::L) R)
  rw [show 1+2*a+4=2*a+5 by omega] at h
  rw [show 2*a+3=3+2*a by omega,zAdd 3 (2*a)]
  simpa only [List.append_assoc,show Z 3=[false,false,false] by rfl] using h

/-- Even run followed by three explicit zeros; B0 writes the new marker. -/
theorem evenZero (L R : List Bool) : run0 table 6 ⟨0,false::L,[false,false,false]++R⟩ =
    some ⟨0,true::L,[true,true,true]++R⟩ := by rfl

theorem evenTurn (L R : List Bool) : run0 table 7 ⟨1,true::L,[true,false,false,false]++R⟩ =
    some ⟨0,[false,false]++L,[true,true,true]++R⟩ := by rfl

theorem evenEpoch (a : Nat) (L R : List Bool) :
    run0 table (2*a+6) ⟨0,false::L,U (2*a)++Z 3++R⟩ =
    some ⟨0,Z (2*a)++true::L,U 3++R⟩ := by
  cases a with
  | zero => exact evenZero L R
  | succ a =>
    have h1 := eraseOdd a L (true::(Z 3++R))
    have h2 := evenTurn (Z (2*a)++true::L) R
    have h := join0 h1 h2
    rw [show 1+2*a+7=2*(a+1)+6 by omega] at h
    have hin : U (2*(a+1)) = U (2*a+1)++[true] := by
      change U (2*(a+1)) = U (2*a+1)++U 1
      rw [List.replicate_append_replicate]; congr 1 <;> omega
    rw [hin]
    have hz : Z (2*(a+1)) = Z 2 ++ Z (2*a) := by rw [show 2*(a+1)=2+2*a by omega,zAdd]
    rw [hz]
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show Z 2=[false,false] by rfl,show U 3=[true,true,true] by rfl] using h

/-- Odd run with no explicit cells beyond it, growing into implicit blanks. -/
theorem oddBlankTurn (L : List Bool) : run0 table 3 ⟨1,true::L,[]⟩ =
    some ⟨3,[false,false,false,false]++L,[]⟩ := by rfl

theorem oddBlank (a : Nat) (L : List Bool) :
    run0 table (4*a+9) ⟨0,false::L,U (2*a+1)⟩ = some ⟨0,L,U (2*a+5)⟩ := by
  have h1 := eraseOdd a L []
  rw [List.append_nil] at h1
  have h2 := oddBlankTurn (Z (2*a)++true::L)
  have h2' : run0 table 3 ⟨1,true::(Z (2*a)++true::L),[]⟩ =
      some ⟨3,Z (2*a+4)++true::L,[]⟩ := by
    rw [show 2*a+4=4+2*a by omega,zAdd 4 (2*a)]
    simpa only [List.append_assoc,show Z 3=[false,false,false] by rfl,show Z 4=[false,false,false,false] by rfl] using h2
  have h3 := dSweep (2*a+4) L []
  rw [List.append_nil] at h3
  have H := join0 (join0 h1 h2') h3
  rw [show 1+2*a+3+(2*a+4+1)=4*a+9 by omega] at H
  rw [show 2*a+5=(2*a+4)+1 by omega,uSucc (2*a+4)]
  exact H

theorem oddBlankEmpty (a : Nat) :
    run0 table (4*a+9) ⟨0,[],U (2*a+1)⟩ = some ⟨0,[],U (2*a+5)⟩ := by
  have h := oddBlank a []
  have he : ∀ n R, run0 table (n+1) ⟨0,[],R⟩ = run0 table (n+1) ⟨0,[false],R⟩ := by
    intro n R
    rfl
  rw [show 4*a+9=(4*a+8)+1 by omega,he]
  exact h

#print axioms oddMany
#print axioms leftMany
#print axioms transferMany
#print axioms oddOne
#print axioms oddTwo
#print axioms evenEpoch
#print axioms oddBlankEmpty
end BB6.Agent19Raw40.A0RC492
