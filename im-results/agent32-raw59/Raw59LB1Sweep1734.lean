import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59LB1Sweep1734
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

abbrev X : List Bool := [true,false]
abbrev U : List Bool := [false,true]
abbrev Y : List Bool := [true,true,false]
abbrev Z : List Bool := [false,true,true]
abbrev P : List Bool := [true,false,false]
abbrev Q : List Bool := [false,true,false]
abbrev V : List Bool := [true,false,true,false]
abbrev W : List Bool := [false,true,false,true]
abbrev F : List Bool := [true,false,true]
abbrev H : List Bool := [true,false,true,false,true]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩

theorem rep_add (a : List Bool) (n m : Nat) : rep a (n+m) = rep a n ++ rep a m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega,rep,ih,rep,List.append_assoc]

theorem shift (a b : List Bool) (k : Nat) : rep (a++b) k ++ a = a ++ rep (b++a) k := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    change ((a++b)++rep (a++b) k) ++ a = a ++ ((b++a)++rep (b++a) k)
    rw [List.append_assoc,ih]
    simp only [List.append_assoc]

theorem align_word (k m : Nat) :
    H ++ rep Z k ++ rep U (m+1) = rep X 3 ++ rep Y k ++ rep X m ++ [true] := by
  have h1 := shift [true] [false] m
  have h2 := shift [false] [true,true] k
  change rep X m ++ [true] = [true] ++ rep U m at h1
  change rep Z k ++ [false] = [false] ++ rep Y k at h2
  rw [rep]
  change H ++ rep Z k ++ ([false] ++ ([true] ++ rep U m)) = _
  rw [← h1, List.append_assoc H (rep Z k), ← List.append_assoc (rep Z k) [false],h2]
  simp only [List.append_assoc]
  rfl

theorem push_word (k : Nat) : X ++ rep Q k = rep P k ++ X := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    change X ++ (Q ++ rep Q k) = P ++ (rep P k ++ X)
    rw [← List.append_assoc X Q,show X++Q=P++X by rfl,List.append_assoc,ih]

theorem left_word (k m : Nat) (R : List Bool) :
    rep X (m+1) ++ (F ++ rep Q k ++ Q ++ R) = rep X (m+3) ++ rep P k ++ X ++ R := by
  simp only [List.append_assoc]
  rw [← List.append_assoc (rep Q k) Q R,rep_snoc Q k,List.append_assoc]
  rw [← List.append_assoc F Q]
  change rep X (m+1) ++ ((rep X 2 ++ X) ++ (rep Q k ++ R)) = _
  simp only [List.append_assoc]
  rw [← List.append_assoc X (rep Q k) R,push_word]
  rw [show m+3=(m+1)+2 by omega,rep_add X (m+1) 2]
  simp only [List.append_assoc]

theorem leftPair (n : Nat) (L R : List Bool) :
    run0 table (4*n) (A (rep X n++L) R) = some (A L (rep X n++R)) := by
  simpa only [List.nil_append] using sweepL table 0 [] [] X X 4 (by intro L R; rfl) n L R

theorem leftTriple (n : Nat) (L R : List Bool) :
    run0 table (17*n) (A (rep Y n++L) (F++R)) = some (A L (F++rep Q n++R)) := by
  simpa only [List.nil_append] using sweepL table 0 [] F Y Q 17 (by intro L R; rfl) n L R

theorem leftPhase (k m : Nat) (R : List Bool) :
    run0 table (12+17*k+4*m+4) (A (rep X 3++rep Y k++rep X m++[true]) R) =
      some (A [] (rep X (m+3)++rep P k++X++R)) := by
  have h1 := leftPair 3 (rep Y k++rep X m++[true]) R
  have h2 := leftTriple k (rep X m++[true]) (Q++R)
  have h3 := leftPair m [true] (F++rep Q k++Q++R)
  have h4 : run0 table 4 (A [true] (rep X m++(F++rep Q k++Q++R))) =
      some (A [] (X++rep X m++(F++rep Q k++Q++R))) := by rfl
  have h1' : run0 table 12 (A (rep X 3++rep Y k++rep X m++[true]) R) =
      some (A (rep Y k++rep X m++[true]) (F++(Q++R))) := by
    have he : rep X 3 ++ R = F ++ (Q++R) := by rfl
    rw [he] at h1
    simpa only [List.append_assoc] using h1
  have h2' : run0 table (17*k) (A (rep Y k++rep X m++[true]) (F++(Q++R))) =
      some (A (rep X m++[true]) (F++rep Q k++Q++R)) := by simpa only [List.append_assoc] using h2
  have h := join0 (join0 (join0 h1' h2') h3) h4
  change run0 table _ _ = some (A [] (rep X (m+1) ++ (F++rep Q k++Q++R))) at h
  rw [left_word] at h
  exact h

theorem rightPair (n : Nat) (L R : List Bool) :
    run0 table (12*n) (A ([false]++L) (rep V n++R)) = some (A ([false]++rep W n++L) R) := by
  simpa only [List.nil_append] using sweepR table 0 [false] [] V W 12 (by intro L R; rfl) n L R

theorem rightFromBlank (n : Nat) (R : List Bool) :
    run0 table (12*(n+1)) (A [] (rep V (n+1)++R)) = some (A ([false]++rep W (n+1)) R) := by
  have h1 : run0 table 12 (A [] (V++rep V n++R)) = some (A ([false]++W) (rep V n++R)) := by rfl
  have h2 := rightPair n W R
  have h := join0 h1 h2
  rw [show 12+12*n=12*(n+1) by omega,List.append_assoc [false] (rep W n) W,rep_snoc W n] at h
  exact h

theorem rightTriple (n : Nat) (L R : List Bool) :
    run0 table (3*n) (A ([false]++L) (rep P n++R)) = some (A ([false]++rep Z n++L) R) := by
  simpa only [List.nil_append] using sweepR table 0 [false] [] P Z 3 (by intro L R; rfl) n L R

theorem paired (a : List Bool) (n : Nat) : rep (a++a) n = rep a (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 2*(n+1)=2*n+1+1 by omega,rep,rep]; simp only [List.append_assoc]

theorem rightPhase (k j : Nat) (R : List Bool) :
    run0 table (12*(j+1)+3*k) (A [] (rep X (2*(j+1))++rep P k++X++R)) =
      some (A ([false]++rep Z k++rep U (2*(j+1))) (X++R)) := by
  have h1 := rightFromBlank j (rep P k++X++R)
  have h2 := rightTriple k (rep W (j+1)) (X++R)
  have h2' : run0 table (3*k) (A ([false]++rep W (j+1)) (rep P k++X++R)) =
      some (A ([false]++rep Z k++rep W (j+1)) (X++R)) := by simpa only [List.append_assoc] using h2
  have h := join0 h1 h2'
  have a := paired X (j+1)
  have b := paired U (j+1)
  change rep V (j+1)=_ at a
  change rep W (j+1)=_ at b
  rw [a,b] at h
  simpa only [List.append_assoc] using h

def family (n : Nat) : Z0 := D ([false]++rep Z (n+2)++rep U (4*(n+1))) []
def epoch (n : Nat) : Nat := 120*(n+1)+101

theorem entry : run0 table 104 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  let k := n+1
  have h0 : run0 table 15 (family n) = some (A (H++rep Z k++rep U (4*k)) [true,true]) := by rfl
  have ha := align_word k (4*n+3)
  have ha' : H++rep Z k++rep U (4*k) = rep X 3++rep Y k++rep X (4*n+3)++[true] := by
    rw [show 4*k=4*n+3+1 by omega]; exact ha
  rw [ha'] at h0
  have h1 := leftPhase k (4*n+3) [true,true]
  rw [show 4*n+3+3=2*(2*n+2+1) by omega] at h1
  have h2 := rightPhase k (2*n+2) [true,true]
  have h3 : run0 table 12 (A ([false]++rep Z k++rep U (2*(2*n+2+1))) (X++[true,true])) =
      some (A (H++rep Z k++rep U (2*(2*n+2+1))) []) := by rfl
  have align2 : H++rep Z k++rep U (2*(2*n+2+1)) = rep X 3++rep Y k++rep X (4*n+5)++[true] := by
    rw [show 2*(2*n+2+1)=4*n+5+1 by omega,align_word]
  rw [align2] at h3
  have h4 := leftPhase k (4*n+5) []
  rw [show 4*n+5+3=2*(2*n+3+1) by omega] at h4
  have h5 := rightPhase k (2*n+3) []
  have h6 : run0 table 6 (A ([false]++rep Z k++rep U (2*(2*n+3+1))) (X++[])) =
      some (family (n+1)) := by
    unfold family
    rw [show 4*(n+1+1)=2*(2*n+3+1) by omega,show n+1+2=k+1+1 by omega]
    rfl
  have h := join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6
  rw [show 15+(12+17*k+4*(4*n+3)+4)+(12*(2*n+2+1)+3*k)+12+(12+17*k+4*(4*n+5)+4)+(12*(2*n+3+1)+3*k)+6=epoch n by unfold epoch; omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 104 epoch entry (by intro n; unfold epoch; omega) growth m hm

#print axioms never
#print axioms growth
#print axioms entry
end BB6.Agent32Raw59LB1Sweep1734
