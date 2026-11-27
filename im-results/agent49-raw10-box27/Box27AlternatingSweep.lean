import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27AlternatingSweep
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,5⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,false,5⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | (5,true) => some (some ⟨false,false,1⟩)
  | _ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
abbrev P := bits "0110101101"
abbrev Q := bits "0100101001"
abbrev T := bits "011011"
abbrev U := bits "01101"
abbrev P0 := bits "011010110"
abbrev P' := bits "1011010110"
def even (n : Nat) : Z0 := ⟨0,bits "0101"++rep P n,[]⟩
def odd (n : Nat) : Z0 := ⟨0,bits "0101"++rep P n++T,[]⟩

theorem first : run0 table 10 ⟨0,[],[]⟩ = some (even 0) := by rfl

theorem enter (L : List Bool) : run0 table 1 ⟨0,bits "0101"++L,[]⟩ = some ⟨1,bits "01101"++L,[]⟩ := by rfl

theorem sweep_left (L R : List Bool) :
    run0 table 10 ⟨1,bits "01101"++P++L,R⟩ = some ⟨1,bits "01101"++L,Q++R⟩ := by rfl

theorem turn_even (R : List Bool) :
    run0 table 18 ⟨1,bits "01101",R⟩ = some ⟨5,bits "01",bits "101001"++R⟩ := by rfl

theorem sweep_right_even (L R : List Bool) :
    run0 table 22 ⟨5,bits "0"++L,bits "101001"++Q++R⟩ =
    some ⟨5,bits "0"++P++L,bits "101001"++R⟩ := by rfl

theorem finish_even (L : List Bool) :
    run0 table 14 ⟨5,bits "0"++L,bits "101001"⟩ = some ⟨0,bits "010101101"++L,[]⟩ := by rfl

theorem turn_odd (R : List Bool) :
    run0 table 12 ⟨1,bits "01101"++T,R⟩ = some ⟨0,bits "11",Q++R⟩ := by rfl

theorem sweep_right_odd (L R : List Bool) :
    run0 table 22 ⟨0,bits "1"++L,Q++Q++R⟩ = some ⟨0,bits "1"++P'++L,Q++R⟩ := by rfl

theorem finish_odd (L : List Bool) :
    run0 table 24 ⟨0,bits "1"++L,Q⟩ = some ⟨0,bits "0101011010110"++L,[]⟩ := by rfl

theorem commute (n : Nat) : U++rep P n = rep P n++U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change P++(U++rep P n) = P++(rep P n++U)
    rw [ih]

theorem even_to_odd (n : Nat) : run0 table (33+32*n) (even n) = some (odd n) := by
  have h1 := enter (rep P n)
  have h2 := sweepL table 1 (bits "01101") [] P Q 10 (by intro L R; simpa using sweep_left L R) n [] []
  have h3 := turn_even (rep Q n)
  have h4 := sweepR table 5 (bits "0") (bits "101001") Q P 22 sweep_right_even n [true] []
  have h5 := finish_even (rep P n++[true])
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3 h4 h5
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 1+10*n+18+22*n+14=33+32*n by omega] at H
  have he : bits "010101101"++(rep P n++[true]) = bits "0101"++(rep P n++T) := by
    change bits "0101"++(U++(rep P n++[true])) = _
    rw [← List.append_assoc U (rep P n) [true],commute]
    simp only [List.append_assoc]; rfl
  rw [he] at H
  simpa only [even,odd,List.append_assoc] using H

theorem odd_to_even (n : Nat) : run0 table (37+32*n) (odd n) = some (even (n+1)) := by
  have h1 := enter (rep P n++T)
  have h2 := sweepL table 1 (bits "01101") [] P Q 10 (by intro L R; simpa using sweep_left L R) n T []
  have h3 := turn_odd (rep Q n)
  have h4 := sweepR table 0 (bits "1") Q Q P' 22 sweep_right_odd n [true] []
  have h5 := finish_odd (rep P' n++[true])
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3 h4 h5
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 1+10*n+12+22*n+24=37+32*n by omega] at H
  have he : bits "0101011010110"++(rep P' n++[true]) = bits "0101"++rep P (n+1) := by
    change bits "0101"++(P0++(rep ([true]++P0) n++[true])) = _
    rw [← rotate true P0 n]
    simp only [rep,List.append_assoc]; rfl
  rw [he] at H
  simpa only [even,odd,List.append_assoc] using H

theorem growth (n : Nat) : run0 table (70+64*n) (even n) = some (even (n+1)) := by
  have H := join0 (even_to_odd n) (odd_to_even n)
  rw [show 33+32*n+(37+32*n)=70+64*n by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table even 10 (fun n => 70+64*n) first (by intro n; omega) growth m hm

#print axioms growth
#print axioms never
end BB6.Agent49.Box27AlternatingSweep
