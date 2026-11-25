import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Raw13Pump0
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none


private def P : List Bool := [true,false]
private def Q : List Bool := [true,true]
def family (n : Nat) : Z0 := ⟨0,[],rep P (2*n+1) ++ [true]⟩

theorem first : run0 table 5 ⟨0,[],[]⟩ = some (family 0) := by rfl
private theorem startRight (R : List Bool) :
    run0 table 2 ⟨0,[],P++R⟩ = some ⟨0,[false]++Q,R⟩ := by rfl
private theorem rightPair (L R : List Bool) :
    run0 table 2 ⟨0,[false]++L,P++R⟩ = some ⟨0,[false]++Q++L,R⟩ := by rfl
private theorem rightEnd (L : List Bool) :
    run0 table 2 ⟨0,[false]++L,[true]⟩ = some ⟨0,[false]++Q++L,[]⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 3 ⟨0,[false]++L,[]⟩ = some ⟨0,Q++L,[true]⟩ := by rfl
private theorem leftPair (L R : List Bool) :
    run0 table 2 ⟨0,Q++L,R⟩ = some ⟨0,L,P++R⟩ := by rfl

theorem growth (n : Nat) : run0 table (8*n+13) (family n) = some (family (n+1)) := by
  have h1 := startRight (rep P (2*n) ++ [true])
  have h2 := sweepR table 0 [false] [] P Q 2 rightPair (2*n) Q [true]
  simp only [List.nil_append] at h2
  have h3 := rightEnd (rep Q (2*n) ++ Q)
  have h4 := turn (Q ++ (rep Q (2*n) ++ Q))
  have h5 := sweepL table 0 [] [] Q P 2 leftPair (2*n+3) [] [true]
  simp only [List.nil_append,List.append_nil] at h5
  have h4' : run0 table 3 ⟨0,[false]++Q++(rep Q (2*n)++Q),[]⟩ =
      some ⟨0,rep Q (2*n+3),[true]⟩ := by
    simpa only [List.append_assoc,rep_snoc,rep] using h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4') h5
  rw [show 2+2*(2*n)+2+3+2*(2*n+3)=8*n+13 by omega] at h
  unfold family
  rw [show 2*(n+1)+1=2*n+3 by omega]
  simpa only [rep,List.append_assoc] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 5 (fun n => 8*n+13) first (by intro n; omega) growth m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0

namespace BB6Coverage.Agent31Pump.Raw13Pump14
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none


private def P : List Bool := [false,true]
private def Q : List Bool := [true,true]
private def T : List Bool := [true,false]
private def frame : List Bool := [false,false,true]

def family (k : Nat) : Z0 := ⟨4,[],T++rep Q (k+1)⟩
theorem first : run0 table 22 ⟨0,[],[]⟩ = some (family 2) := by rfl
private theorem startRight (R : List Bool) :
    run0 table 2 ⟨4,[],T++R⟩ = some ⟨4,frame,R⟩ := by rfl
private theorem rightPair (L R : List Bool) :
    run0 table 4 ⟨4,frame++L,Q++Q++R⟩ = some ⟨4,frame++P++L,Q++R⟩ := by rfl
private theorem rightEnd (L : List Bool) :
    run0 table 2 ⟨4,frame++L,Q⟩ = some ⟨4,[true]++P++P++L,[]⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 6 ⟨4,[true]++P++P++L,[]⟩ = some ⟨0,[true]++P++P++P++L,[true]⟩ := by rfl

private theorem leftPair (L R : List Bool) :
    run0 table 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem leftEnd (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 3 ⟨0,[],[true]++R⟩ = some ⟨4,[],T++R⟩ := by rfl
private theorem rotateP (n : Nat) : [true]++rep P n = rep T n++[true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,false] ++ ([true]++rep P n) = [true,false] ++ (rep T n++[true])
    rw [ih]
private theorem commuteQ (n : Nat) : [true]++rep Q n = rep Q n++[true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true] ++ ([true]++rep Q n) = [true,true] ++ (rep Q n++[true])
    rw [ih]

theorem growth (k : Nat) : run0 table (6*k+21) (family k) = some (family (k+3)) := by
  have h1 := startRight (rep Q (k+1))
  have h2 := sweepR table 4 frame Q Q P 4 rightPair k [] []
  simp only [List.append_nil] at h2
  have h3 := rightEnd (rep P k)
  have h4 := turn (rep P k)
  have h4' : run0 table 6 ⟨4,[true]++P++P++rep P k,[]⟩ =
      some ⟨0,rep T (k+3)++[true],[true]⟩ := by
    rw [← rotateP]
    simpa only [rep,List.append_assoc] using h4
  have h5 := sweepL table 0 [] [] T Q 2 leftPair (k+3) [true] [true]
  simp only [List.nil_append] at h5
  have h6 := leftEnd (rep Q (k+3)++[true])
  have h7' : run0 table 3 ⟨0,[],Q++(rep Q (k+3)++[true])⟩ =
      some (family (k+3)) := by
    unfold family
    have hx : [true]++rep Q (k+4) = Q++(rep Q (k+3)++[true]) := by
      rw [commuteQ]
      rfl
    rw [← hx]
    exact finish (rep Q (k+4))
  have h := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4') h5) h6) h7'
  rw [show 2+4*k+2+6+2*(k+3)+2+3=6*k+21 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun n => family (3*n+2)) 22 (fun n => 6*(3*n+2)+21) first
  · intro n; omega
  · intro n
    simpa only [show 3*(n+1)+2 = (3*n+2)+3 by omega] using growth (3*n+2)
  · exact hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump14

namespace BB6Coverage.Agent31Pump.Raw13Pump12
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none


private def P : List Bool := [false,true]
private def Q : List Bool := [true,true]
private def T : List Bool := [true,false]
private def frame : List Bool := [false,false,true]

def family (a b : Nat) : Z0 := ⟨4,[],rep T (a+1)++rep Q (b+1)⟩
theorem first : run0 table 22 ⟨0,[],[]⟩ = some (family 0 2) := by rfl
private theorem startRight (R : List Bool) :
    run0 table 2 ⟨4,[],T++R⟩ = some ⟨4,frame,R⟩ := by rfl
private theorem rightPair (L R : List Bool) :
    run0 table 2 ⟨4,frame++L,T++R⟩ = some ⟨4,frame++P++L,R⟩ := by rfl
private theorem rightEnd (L R : List Bool) :
    run0 table 2 ⟨4,frame++L,Q++R⟩ = some ⟨4,[true]++P++P++L,R⟩ := by rfl
private theorem backPair (L R : List Bool) :
    run0 table 6 ⟨4,[true]++P++L,[true]++R⟩ = some ⟨4,[true]++L,[true]++P++R⟩ := by rfl
private theorem backEnd (R : List Bool) :
    run0 table 6 ⟨4,[true],[true]++R⟩ = some ⟨4,[],T++[true]++R⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 14 ⟨4,[true]++P++P++L,[]⟩ = some ⟨0,[true]++P++P++P++P++L,[true]⟩ := by rfl

private theorem leftPair (L R : List Bool) :
    run0 table 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem leftEnd (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 3 ⟨0,[],[true]++R⟩ = some ⟨4,[],T++R⟩ := by rfl
private theorem rotateP (n : Nat) : [true]++rep P n = rep T n++[true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,false] ++ ([true]++rep P n) = [true,false] ++ (rep T n++[true])
    rw [ih]
private theorem commuteQ (n : Nat) : [true]++rep Q n = rep Q n++[true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true] ++ ([true]++rep Q n) = [true,true] ++ (rep Q n++[true])
    rw [ih]

private theorem scan (a b : Nat) :
    run0 table (2+2*a+2) (family a b) = some ⟨4,[true]++rep P (a+2),rep Q b⟩ := by
  have h1 := startRight (rep T a++rep Q (b+1))
  have h2 := sweepR table 4 frame [] T P 2 rightPair a [] (rep Q (b+1))
  simp only [List.nil_append,List.append_nil] at h2
  have h3 := rightEnd (rep P a) (rep Q b)
  have h := join0 (join0 h1 h2) h3
  simpa only [family,rep,List.append_assoc] using h

theorem growthPos (a b : Nat) :
    run0 table (8*a+22) (family a (b+1)) = some (family (a+2) b) := by
  have h1 := scan a (b+1)
  have h2 := sweepL table 4 [true] [true] P P 6 backPair (a+2) [] ([true]++rep Q b)
  simp only [List.append_nil] at h2
  have h3 := backEnd (rep P (a+2)++([true]++rep Q b))
  have h := join0 (join0 h1 h2) h3
  rw [show 2+2*a+2+6*(a+2)+6=8*a+22 by omega] at h
  have hh : T++([true]++(rep P (a+2)++([true]++rep Q b))) =
      rep T (a+3)++rep Q (b+1) := by
    rw [← List.append_assoc [true] (rep P (a+2)) ([true]++rep Q b), rotateP]
    simp only [rep,List.append_assoc]
    rfl
  rw [show T++[true]++(rep P (a+2)++([true]++rep Q b)) =
      T++([true]++(rep P (a+2)++([true]++rep Q b))) by simp only [List.append_assoc],hh] at h
  exact h

theorem growthZero (a : Nat) :
    run0 table (4*a+31) (family a 0) = some (family 0 (a+4)) := by
  have h1 := scan a 0
  have h2 := turn (rep P a)
  have h2' : run0 table 14 ⟨4,[true]++rep P (a+2),[]⟩ =
      some ⟨0,rep T (a+4)++[true],[true]⟩ := by
    rw [← rotateP]
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 0 [] [] T Q 2 leftPair (a+4) [true] [true]
  simp only [List.nil_append] at h3
  have h4 := leftEnd (rep Q (a+4)++[true])
  have h5 : run0 table 3 ⟨0,[],Q++(rep Q (a+4)++[true])⟩ = some (family 0 (a+4)) := by
    unfold family
    have hx : [true]++rep Q (a+5) = Q++(rep Q (a+4)++[true]) := by
      rw [commuteQ]
      rfl
    rw [← hx]
    exact finish (rep Q (a+5))
  have h := join0 (join0 (join0 (join0 h1 h2') h3) h4) h5
  rw [show 2+2*a+2+14+2*(a+4)+2+3=4*a+31 by omega] at h
  exact h

def next : Nat × Nat → Nat × Nat
  | (a,0) => (0,a+4)
  | (a,b+1) => (a+2,b)
def cost : Nat × Nat → Nat
  | (a,0) => 4*a+31
  | (a,_+1) => 8*a+22
def params : Nat → Nat × Nat
  | 0 => (0,2)
  | n+1 => next (params n)
private theorem step (a b : Nat) :
    run0 table (cost (a,b)) (family a b) =
      some (family (next (a,b)).1 (next (a,b)).2) := by
  cases b with
  | zero => exact growthZero a
  | succ b => exact growthPos a b
private theorem positive (a b : Nat) : 0 < cost (a,b) := by
  cases b <;> simp [cost]

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => family (params n).1 (params n).2) 22
    (fun n => cost (params n)) first
    (fun n => positive (params n).1 (params n).2)
    (fun n => step (params n).1 (params n).2) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump12
