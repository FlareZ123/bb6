import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6OneLF9135
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def X : List Bool := [true,true,false,true,false]
def Y : List Bool := [false,false,true,true,true]
def Z : List Bool := [false,true,false,true,true]
def F (k : Nat) : Z0 := ⟨0,[],[true,true,false,true,false,true,true,true,false,true,false]++rep X k++[true,true,false,true]⟩
theorem setup (R : List Bool) :
    run0 p 11 ⟨0,[],[true,true,false,true,false,true,true,true,false,true,false]++R⟩ =
      some ⟨0,[false,true,true]++[false,false,false,true,true,true,false,false,true],R⟩ := rfl
theorem right5 (L R : List Bool) :
    run0 p 5 ⟨0,[false,true,true]++L,X++R⟩ =
      some ⟨0,[false,true,true]++Y++L,R⟩ := rfl
theorem turn20 (L : List Bool) :
    run0 p 20 ⟨0,[false,true,true]++L,[true,true,false,true]⟩ =
      some ⟨0,[true,true,true]++L,[true,true,false]++[true,true,true,true]⟩ := rfl
theorem left17 (L R : List Bool) :
    run0 p 17 ⟨0,[true,true,true]++Y++L,[true,true,false]++R⟩ =
      some ⟨0,[true,true,true]++L,[true,true,false]++X++R⟩ := rfl
theorem bridge24 (R : List Bool) :
    run0 p 24 ⟨0,[true,true,true]++[false,false,false,true,true,true,false,false,true],[true,true,false]++R⟩ =
      some ⟨0,[false,true,true]++Y++[true,false,false,true],[true,true,false]++R⟩ := rfl
theorem right7 (L R : List Bool) :
    run0 p 7 ⟨0,[false,true,true]++L,[true,true,false,true,true]++Z++R⟩ =
      some ⟨0,[false,true,true]++Y++L,[true,true,false,true,true]++R⟩ := rfl
theorem turn22 (L : List Bool) :
    run0 p 22 ⟨0,[false,true,true]++L,[true,true,false,true,true,true,true]⟩ =
      some ⟨0,[true,true,true]++L,[true,true,false]++[true,true,false,true]⟩ := rfl
theorem finish28 (R : List Bool) :
    run0 p 28 ⟨0,[true,true,true]++[true,false,false,true],[true,true,false]++R⟩ =
      some ⟨0,[],[true,true,false,true,false,true,true,true,false,true,false]++R⟩ := rfl
theorem rotate_words (a b : List Bool) (n : Nat) :
    rep (a++b) n++a = a++rep (b++a) n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc] at *; rw [← List.append_assoc (a++b),ih]; simp only [List.append_assoc]
theorem exchange (k : Nat) :
    [true,true,false]++rep X k++[true,true,true,true] = [true,true,false,true,true]++rep Z k++[true,true] := by
  have h := rotate_words [true,true] [false,true,false] k
  change rep X k++[true,true] = [true,true]++rep Z k at h
  rw [show [true,true,true,true]=[true,true]++[true,true] by rfl,← List.append_assoc (rep X k),List.append_assoc [true,true,false],h]
  simp only [List.append_assoc,List.cons_append,List.nil_append]
theorem growth (k : Nat) :
    run0 p (46*k+122) (F k)=some (F (k+1)) := by
  have h0 := setup (rep X k++[true,true,false,true])
  have h1 := sweepR p 0 [false,true,true] [] X Y 5 right5 k [false,false,false,true,true,true,false,false,true] [true,true,false,true]
  have h2 := turn20 (rep Y k++[false,false,false,true,true,true,false,false,true])
  have h3 := sweepL p 0 [true,true,true] [true,true,false] Y X 17 left17 k [false,false,false,true,true,true,false,false,true] [true,true,true,true]
  have h4 := bridge24 (rep X k++[true,true,true,true])
  have h5 := sweepR p 0 [false,true,true] [true,true,false,true,true] Z Y 7 right7 k (Y++[true,false,false,true]) [true,true]
  have h6 := turn22 (rep Y (k+1)++[true,false,false,true])
  have h7 := sweepL p 0 [true,true,true] [true,true,false] Y X 17 left17 (k+1) [true,false,false,true] [true,true,false,true]
  have h8 := finish28 (rep X (k+1)++[true,true,false,true])
  simp only [List.nil_append,List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have H := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [← List.append_assoc [true,true,false],exchange] at H
  have J := join0 H h5
  have h5' : rep Y k++Y++[true,false,false,true] = rep Y (k+1)++[true,false,false,true] := by rw [← List.append_assoc,rep_snoc]; rfl
  rw [h5'] at J
  have K := join0 (join0 (join0 J h6) h7) h8
  rw [show 11+5*k+20+17*k+24+7*k+22+17*(k+1)+28=46*k+122 by omega] at K
  simpa only [F,List.append_assoc] using K
theorem seed : run0 p 119 ⟨0,[],[]⟩ = some (F 0) := rfl
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_pad_growth p F 119 (fun k => 46*k+122) (exactRun seed)
    (by intro k; omega) (fun k => exactRun (growth k)) m hm
#print axioms never
end BB6.Agent6OneLF9135
