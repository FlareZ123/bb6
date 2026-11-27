import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27HardGrowth
open BB6Coverage BB6Coverage.Agent31Pump

namespace M0
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,0⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,true,4⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨true,false,0⟩)
  | (4,true) => some (some ⟨false,false,5⟩)
  | (5,true) => some (some ⟨true,true,0⟩)
  | _ => none
abbrev alt : List Bool := [true,false,true,false]
abbrev ones : List Bool := [true,true,true,true]
def family (n : Nat) : Z0 := ⟨0,[],[true,false,false] ++ rep alt n ++ [true,false,true]⟩
theorem first : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem enter (R : List Bool) : run0 table 5 ⟨0,[],[true,false,false]++R⟩ = some ⟨0,[false,true,true,true],R⟩ := by rfl
theorem rightLoop (L R : List Bool) : run0 table 6 ⟨0,[false]++L,alt++R⟩ = some ⟨0,[false]++ones++L,R⟩ := by rfl
theorem rightEnd (L : List Bool) : run0 table 6 ⟨0,[false]++L,[true,false,true]⟩ = some ⟨0,[false,true,true,true,true]++L,[]⟩ := by rfl
theorem turn (L : List Bool) : run0 table 6 ⟨0,[false,true,true,true,true]++L,[]⟩ = some ⟨0,[false,true,true]++L,[false,false,true]⟩ := by rfl
theorem leftLoop (L R : List Bool) : run0 table 12 ⟨0,[false,true,true]++ones++L,[false,false]++R⟩ = some ⟨0,[false,true,true]++L,[false,false]++alt++R⟩ := by rfl
theorem leftEnd (R : List Bool) : run0 table 12 ⟨0,[false,true,true,true,true,true],[false,false]++R⟩ = some ⟨0,[false,true],[false,false]++alt++R⟩ := by rfl
theorem finish (R : List Bool) : run0 table 5 ⟨0,[false,true],[false,false]++R⟩ = some ⟨0,[],[true,false,false,true,false]++R⟩ := by rfl
theorem commute (n : Nat) : [true,false] ++ rep alt n = rep alt n ++ [true,false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change alt ++ ([true,false] ++ rep alt n) = alt ++ (rep alt n ++ [true,false])
    rw [ih]
theorem growth (n : Nat) : run0 table (34+18*n) (family n) = some (family (n+1)) := by
  have h1 := enter (rep alt n ++ [true,false,true])
  have h2 := sweepR table 0 [false] [] alt ones 6 (by intro L R; simpa using rightLoop L R) n [true,true,true] [true,false,true]
  have h3 := rightEnd (rep ones n ++ [true,true,true])
  have h4 := turn (rep ones n ++ [true,true,true])
  have h5 := sweepL table 0 [false,true,true] [false,false] ones alt 12 leftLoop n [true,true,true] [true]
  have h6 := leftEnd (rep alt n ++ [true])
  have h7 := finish (alt ++ rep alt n ++ [true])
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5 h6 h7
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  rw [show 5+6*n+6+6+12*n+12+5=34+18*n by omega] at H
  unfold family
  simp only [List.append_assoc] at H ⊢
  have he : [true,false,false,true,false] ++ (alt ++ (rep alt n ++ [true])) = [true,false,false] ++ (rep alt (n+1) ++ [true,false,true]) := by
    simp only [rep,List.append_assoc]
    change [true,false,false] ++ (alt ++ ([true,false] ++ (rep alt n ++ [true]))) = [true,false,false] ++ (alt ++ (rep alt n ++ [true,false,true]))
    rw [← List.append_assoc [true,false] (rep alt n) [true],commute]
    simp only [List.append_assoc]
    rfl
  rw [he] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 34+18*n) first (by intro n; omega) growth m hm
#print axioms never
end M0

namespace M2
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,3⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨false,true,5⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨true,false,0⟩)
  | (4,true) => some (some ⟨false,true,0⟩)
  | (5,false) => some (some ⟨true,true,4⟩)
  | _ => none
abbrev a : List Bool := [true,false,true,false]
abbrev b : List Bool := [false,true,false,true]
def family (n : Nat) : Z0 := ⟨4,[false]++rep a n++[true,false,true],[]⟩
theorem first : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem leftLoop (L R : List Bool) : run0 table 8 ⟨4,[false]++a++L,R⟩ = some ⟨4,[false]++L,b++R⟩ := by rfl
theorem leftEnd (R : List Bool) : run0 table 9 ⟨4,b,R⟩ = some ⟨0,[],[true,false,true,false,true]++R⟩ := by rfl
theorem rightBegin (R : List Bool) : run0 table 4 ⟨0,[],a++R⟩ = some ⟨0,[false,false,true,false,true],R⟩ := by rfl
theorem rightLoop (L R : List Bool) : run0 table 4 ⟨0,[false]++L,a++R⟩ = some ⟨0,[false]++b++L,R⟩ := by rfl
theorem rightEnd (L : List Bool) : run0 table 3 ⟨0,[false]++L,[true]⟩ = some ⟨4,b++L,[]⟩ := by rfl
theorem growth (n : Nat) : run0 table (16+12*n) (family n) = some (family (n+1)) := by
  have h1 := sweepL table 4 [false] [] a b 8 (by intro L R; simpa using leftLoop L R) n [true,false,true] []
  have h2 := leftEnd (rep b n)
  have h3 := rightBegin ([true] ++ rep b n)
  have hr : [true] ++ rep b n = rep a n ++ [true] := rotate true [false,true,false] n
  have h4 := sweepR table 0 [false] [] a b 4 (by intro L R; simpa using rightLoop L R) n b [true]
  have h5 := rightEnd (rep b n ++ b)
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3 h4 h5
  have H0 := join0 (join0 h1 h2) h3
  rw [hr] at H0
  have H := join0 (join0 H0 h4) h5
  rw [show 8*n+9+4+4*n+3=16+12*n by omega] at H
  unfold family
  simp only [List.append_assoc] at H ⊢
  have rot (k : Nat) : [true,false,true] ++ rep b k = rep a k ++ [true,false,true] := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [rep,List.append_assoc]
      change a ++ ([true,false,true] ++ rep b k) = a ++ (rep a k ++ [true,false,true])
      rw [ih]
  have htarget : b ++ (rep b n ++ b) = [false] ++ (rep a (n+1) ++ [true,false,true]) := by
    rw [rep_snoc b n]
    change [false] ++ ([true,false,true] ++ rep b (n+1)) = [false] ++ (rep a (n+1) ++ [true,false,true])
    rw [rot]
  rw [htarget] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 16+12*n) first (by intro n; omega) growth m hm
#print axioms never
end M2

namespace M4
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,3⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,true,5⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨true,false,0⟩)
  | (4,true) => some (some ⟨true,false,3⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | _ => none
abbrev a : List Bool := [true,false,true,false,true,false]
abbrev b : List Bool := [true,true,true,true,true,true]
abbrev pre : List Bool := [true,false,true,false,false,true,false]
abbrev suf : List Bool := [true,false,false,true]
def family (n : Nat) : Z0 := ⟨0,[],pre++rep a n++suf⟩
theorem first : run0 table 54 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem enter (R : List Bool) : run0 table 11 ⟨0,[],pre++R⟩ = some ⟨0,[false,true,true,true,false,true,true,true],R⟩ := by rfl
theorem rightLoop (L R : List Bool) : run0 table 10 ⟨0,[false]++L,a++R⟩ = some ⟨0,[false]++b++L,R⟩ := by rfl
theorem turn (L : List Bool) : run0 table 9 ⟨0,[false]++L,suf⟩ = some ⟨3,[true,true,true,true,true,true]++L,[false,true]⟩ := by rfl
theorem leftLoop (L R : List Bool) : run0 table 6 ⟨3,[true]++b++L,R⟩ = some ⟨3,[true]++L,a++R⟩ := by rfl
theorem leftEnd (R : List Bool) : run0 table 8 ⟨3,[true,true,true,true,true,true,true,true,true,false,true,true,true],R⟩ = some ⟨3,[true,false,true,true,true],[true,false,true,false,true,false,true,false]++R⟩ := by rfl
theorem finish (R : List Bool) : run0 table 21 ⟨3,[true,false,true,true,true],[true]++R⟩ = some ⟨0,[],pre++[true]++R⟩ := by rfl
theorem commute (n : Nat) : [true,false] ++ rep a n = rep a n ++ [true,false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change a ++ ([true,false] ++ rep a n) = a ++ (rep a n ++ [true,false])
    rw [ih]
theorem growth (n : Nat) : run0 table (49+16*n) (family n) = some (family (n+1)) := by
  have h1 := enter (rep a n ++ suf)
  have h2 := sweepR table 0 [false] [] a b 10 (by intro L R; simpa using rightLoop L R) n [true,true,true,false,true,true,true] suf
  have h3 := turn (rep b n ++ [true,true,true,false,true,true,true])
  have h4 := sweepL table 3 [true] [] b a 6 (by intro L R; simpa using leftLoop L R) n [true,true,true,true,true,true,true,true,false,true,true,true] [false,true]
  have hb (k : Nat) : [true,true,true,true,true] ++ rep b k = rep b k ++ [true,true,true,true,true] := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [rep,List.append_assoc]
      change b ++ ([true,true,true,true,true] ++ rep b k) = b ++ (rep b k ++ [true,true,true,true,true])
      rw [ih]
  have h5 := leftEnd (rep a n ++ [false,true])
  have h6 := finish ([false,true,false,true,false,true,false]++rep a n++[false,true])
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5 h6
  have H0 := join0 (join0 h1 h2) h3
  have hmove : [true,true,true,true,true,true] ++ (rep b n ++ [true,true,true,false,true,true,true]) = [true] ++ (rep b n ++ [true,true,true,true,true,true,true,true,false,true,true,true]) := by
    change [true] ++ ([true,true,true,true,true] ++ (rep b n ++ [true,true,true,false,true,true,true])) = _
    rw [← List.append_assoc [true,true,true,true,true] (rep b n),hb]
    simp only [List.append_assoc]
    rfl
  rw [hmove] at H0
  have H := join0 (join0 (join0 H0 h4) h5) h6
  rw [show 11+10*n+9+6*n+8+21=49+16*n by omega] at H
  unfold family
  simp only [List.append_assoc] at H ⊢
  have htarget : pre ++ [true] ++ ([false,true,false,true,false,true,false] ++ (rep a n ++ [false,true])) = pre ++ (rep a (n+1) ++ suf) := by
    simp only [rep,List.append_assoc]
    change pre ++ (a ++ ([true,false] ++ (rep a n ++ [false,true]))) = pre ++ (a ++ (rep a n ++ suf))
    rw [← List.append_assoc [true,false] (rep a n),commute]
    simp only [List.append_assoc]
    rfl
  simp only [List.append_assoc] at htarget
  rw [htarget] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 54 (fun n => 49+16*n) first (by intro n; omega) growth m hm
#print axioms never
end M4
end BB6.Agent49.Box27HardGrowth
