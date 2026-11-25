import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump1RE
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
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
private def P : List Bool := [false,true]
private def T : List Bool := [true,false]
private def Q : List Bool := [true,true]
private def A (n : Nat) : Z0 := ⟨0,[],rep Q (n+8) ++ [true]⟩
private def D (a b : Nat) : Z0 := ⟨3,[],rep P (a+1)++rep Q b++[true]⟩
private def End (a : Nat) : Z0 := ⟨3,[],rep P (a+1)++[false]⟩
theorem first : run0 table 663 ⟨0,[],[]⟩ = some (A 6) := by rfl
private theorem pre (R : List Bool) :
    run0 table 120 ⟨0,[],rep Q 8++R⟩ = some ⟨3,[],rep P 9++R⟩ := by rfl
private theorem start (R : List Bool) :
    run0 table 3 ⟨3,[],P++R⟩ = some ⟨1,[false,false,true],[true]++R⟩ := by rfl
private theorem rightPair (L R : List Bool) :
    run0 table 2 ⟨1,[false,false]++L,[true]++P++R⟩ =
      some ⟨1,[false,false]++T++L,[true]++R⟩ := by rfl
private theorem turnPos (L R : List Bool) :
    run0 table 3 ⟨1,[false,false]++L,[true,true]++R⟩ =
      some ⟨3,[false,true,false]++L,[false]++R⟩ := by rfl
private theorem turnLast (L : List Bool) :
    run0 table 3 ⟨1,[false,false]++L,[true,true]⟩ =
      some ⟨3,[false,true,false]++L,[false]⟩ := by rfl
private theorem leftD (L R : List Bool) :
    run0 table 2 ⟨3,P++L,R⟩ = some ⟨3,L,P++R⟩ := by rfl
private theorem turnZero (L : List Bool) :
    run0 table 4 ⟨1,[false,false]++L,[true,false]⟩ =
      some ⟨0,[true,false,true,false]++L,[true]⟩ := by rfl
private theorem leftA (L R : List Bool) :
    run0 table 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem rep_add (X : List Bool) (a b : Nat) : rep X (a+b)=rep X a++rep X b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,ih,rep,List.append_assoc]
private theorem rotate (a : Nat) : [false]++rep T a++[true]=rep P (a+1) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change P++([false]++rep T a++[true])=P++rep P (a+1)
    rw [ih]
private theorem scan (a : Nat) (R : List Bool) :
    run0 table (3+2*a) ⟨3,[],rep P (a+1)++R⟩ =
      some ⟨1,[false,false]++rep T a++[true],[true]++R⟩ := by
  have h := join0 (start (rep P a++R))
    (sweepR table 1 [false,false] [true] P T 2 rightPair a [true] R)
  simpa only [rep,List.append_assoc] using h
private theorem pos (a b : Nat) : run0 table (4*a+10) (D a (b+1)) = some (D (a+2) b) := by
  have h1 := scan a (rep Q (b+1)++[true])
  have h2 := turnPos (rep T a++[true]) ([true]++rep Q b++[true])
  have h2' : run0 table 3 ⟨1,[false,false]++rep T a++[true],[true]++(rep Q (b+1)++[true])⟩ =
      some ⟨3,rep P (a+2),P++rep Q b++[true]⟩ := by
    have hh : [false,true,false]++(rep T a++[true])=rep P (a+2) := by
      change P++([false]++rep T a++[true])=P++rep P (a+1)
      rw [rotate]
    rw [hh] at h2
    simp only [rep,List.append_assoc] at h2 ⊢
    exact h2
  have h3 := sweepL table 3 [] [] P P 2 leftD (a+2) [] (P++rep Q b++[true])
  simp only [List.nil_append,List.append_nil] at h3
  have h := join0 (join0 h1 h2') h3
  rw [show 3+2*a+3+2*(a+2)=4*a+10 by omega] at h
  have hh : rep P (a+2)++P = rep P (a+2+1) := by
    rw [rep_snoc]
    rfl
  unfold D
  rw [← hh]
  simpa only [List.append_assoc] using h
private theorem last (a : Nat) : run0 table (4*a+10) (D a 0) = some (End (a+1)) := by
  have h1 := scan a [true]
  have h2 := turnLast (rep T a++[true])
  have h2' : run0 table 3 ⟨1,[false,false]++rep T a++[true],[true,true]⟩ =
      some ⟨3,rep P (a+2),[false]⟩ := by
    have hh : [false,true,false]++(rep T a++[true])=rep P (a+2) := by
      change P++([false]++rep T a++[true])=P++rep P (a+1)
      rw [rotate]
    rw [hh] at h2
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 3 [] [] P P 2 leftD (a+2) [] [false]
  simp only [List.nil_append,List.append_nil] at h3
  have h := join0 (join0 h1 h2') h3
  rw [show 3+2*a+3+2*(a+2)=4*a+10 by omega] at h
  simpa only [D,End,rep,List.nil_append,List.append_assoc] using h
private theorem terminal (a : Nat) : run0 table (4*a+13) (End a) =
    some ⟨0,[],rep Q (a+3)++[true]⟩ := by
  have h1 := scan a [false]
  have h2 := turnZero (rep T a++[true])
  have h2' : run0 table 4 ⟨1,[false,false]++rep T a++[true],[true,false]⟩ =
      some ⟨0,rep T (a+2)++[true],[true]⟩ := by
    simp only [rep,List.append_assoc] at h2 ⊢
    exact h2
  have h3 := sweepL table 0 [] [] T Q 2 leftA (a+2) [true] [true]
  simp only [List.nil_append] at h3
  have h4 := finish (rep Q (a+2)++[true])
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 3+2*a+4+2*(a+2)+2=4*a+13 by omega] at h
  simpa only [End,rep,List.append_assoc] using h
private def costD (a : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => 4*a+10+costD (a+2) b
private theorem iterD (a b : Nat) : run0 table (costD a b) (D a b) = some (D (a+2*b) 0) := by
  induction b generalizing a with
  | zero => simp [costD,run0]
  | succ b ih =>
    have h := join0 (pos a b) (ih (a+2))
    simpa only [costD,show a+2+2*b=a+2*(b+1) by omega] using h
private theorem costD_eq (a b : Nat) : costD a b=4*b*b+(4*a+6)*b := by
  induction b generalizing a with
  | zero => simp [costD]
  | succ b ih => rw [costD,ih]; simp only [Nat.mul_add,Nat.add_mul]; omega

theorem growth (n : Nat) : run0 table (4*n*n+54*n+211) (A n) = some (A (2*n+4)) := by
  have h1 := pre (rep Q n++[true])
  have h1' : run0 table 120 (A n) = some (D 8 n) := by
    unfold A D
    rw [Nat.add_comm n 8,rep_add,List.append_assoc]
    exact h1
  have h2 := iterD 8 n
  have h3 := last (8+2*n)
  have h4 := terminal (8+2*n+1)
  have h := join0 (join0 (join0 h1' h2) h3) h4
  rw [costD_eq,show 120+(4*n*n+(4*8+6)*n)+(4*(8+2*n)+10)+(4*(8+2*n+1)+13)=4*n*n+54*n+211 by omega] at h
  simpa only [A,show 8+2*n+1+3=2*n+4+8 by omega] using h

private def orbit : Nat → Nat
  | 0 => 6
  | k+1 => 2*orbit k+4

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun k => A (orbit k)) 663
    (fun k => 4*orbit k*orbit k+54*orbit k+211) first
    (fun k => by omega) (fun k => growth (orbit k)) m hm

#print axioms growth
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump1RE
