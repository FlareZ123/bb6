import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LEE1RFM177
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def J : List Bool := [false,true,false,true]
def I : List Bool := [true,false,true,false]
def O : List Bool := [false,false,false,true]
def T : List Bool := [true,false,true]

def family (k : Nat) : Z0 := ⟨0,[],rep J k⟩
def cost (k : Nat) : Nat := 10*k+11

theorem tailRotate (n : Nat) : T ++ rep J n = rep I n ++ T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      T ++ rep J (n+1) = (T++J) ++ rep J n := by simp only [rep,List.append_assoc]
      _ = (I++T) ++ rep J n := by rfl
      _ = I ++ (T ++ rep J n) := by simp only [List.append_assoc]
      _ = I ++ (rep I n ++ T) := by rw [ih]
      _ = rep I (n+1) ++ T := by simp only [rep,List.append_assoc]

theorem outOne (L R : List Bool) :
    run0 table 4 ⟨1,[false]++L,I++R⟩ =
      some ⟨1,[false]++O++L,R⟩ := by rfl

theorem outMany (n : Nat) (L R : List Bool) :
    run0 table (4*n) ⟨1,[false]++L,rep I n++R⟩ =
      some ⟨1,[false]++rep O n++L,R⟩ := by
  simpa only [List.nil_append] using
    sweepR table 1 [false] [] I O 4 outOne n L R

theorem outLast (L : List Bool) :
    run0 table 4 ⟨1,[false]++L,T⟩ =
      some ⟨1,[false]++O++L,[]⟩ := by rfl

theorem turn (L : List Bool) :
    run0 table 6 ⟨1,[false]++O++L,[]⟩ =
      some ⟨4,[false]++O++L,[false,true]⟩ := by rfl

theorem enterBack (L : List Bool) :
    run0 table 2 ⟨4,[false]++L,[false,true]⟩ =
      some ⟨4,[true]++L,[false,true]⟩ := by rfl

theorem backOne (L R : List Bool) :
    run0 table 6 ⟨4,[true]++O++L,[false,true]++R⟩ =
      some ⟨4,[true]++L,[false,true]++J++R⟩ := by rfl

theorem backMany (n : Nat) (L R : List Bool) :
    run0 table (6*n) ⟨4,[true]++rep O n++L,[false,true]++R⟩ =
      some ⟨4,[true]++L,[false,true]++rep J n++R⟩ := by
  simpa only [List.append_assoc] using
    sweepL table 4 [true] [false,true] O J 6 backOne n L R

theorem finish (L R : List Bool) :
    run0 table 2 ⟨4,[true,true]++L,[false,true]++R⟩ =
      some ⟨0,L,J++R⟩ := by rfl

theorem first : run0 table 0 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (k : Nat) : 0 < cost k := by simp [cost]

theorem growth (k : Nat) :
    run0 table (cost k) (family k) = some (family (k+1)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (family (k+1)) =
        some ⟨1,[false,true],T++rep J k⟩ := by rfl
    have h1' : run0 table 1 (family (k+1)) =
        some ⟨1,[false,true],rep I k++T⟩ := by
      simpa only [tailRotate] using h1
    have h2 := outMany k [true] T
    have h3 := outLast (rep O k++[true])
    have h4 := turn (rep O k++[true])
    have h5 := enterBack (O++rep O k++[true])
    have h6 := backMany (k+1) [true] []
    have h7 := finish [] (rep J (k+1))
    have H := join0 (join0 (join0 (join0 (join0 (join0 h1' h2) h3) h4) h5) h6) h7
    simpa only [family,cost,rep,List.append_assoc,Nat.mul_succ] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 0 cost first positive growth m hm

#print axioms growth
#print axioms never
end BB6.Agent25Raw43B0LEE1RFM177
