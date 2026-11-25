import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0RE
open BB6Coverage Agent31Pump

def table (v : Nat) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some (if v=0 then ⟨false,true,5⟩ else if v=4 then ⟨true,true,4⟩ else ⟨true,true,5⟩))
  | 4,true => some (some (if v=2 then ⟨false,true,0⟩ else if v=4 then ⟨false,true,5⟩ else ⟨true,true,3⟩))
  | 5,true => some (some (if v=3 then ⟨true,false,4⟩ else if v=4 then ⟨false,true,0⟩ else ⟨false,true,4⟩))
  | _,_ => none
private def T : List Bool := [true,false]
private def P : List Bool := [false,true]
private def Q : List Bool := [true,true]
def family (k : Nat) : Z0 := ⟨0,[],[true]++rep Q k⟩
private theorem rot (n : Nat) : [true]++rep P n = rep T n++[true] := by
  exact rotate true [false] n
private theorem qrot (n : Nat) : [true]++rep Q n = rep Q n++[true] := by
  exact rotate true [true] n
private theorem rep_add (X : List Bool) (a b : Nat) : rep X a++rep X b=rep X (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [rep,List.append_assoc,ih,show a+1+b=a+b+1 by omega]
private theorem startE (v k : Nat) : run0 (table v) 3 (family k) = some ⟨4,[false,false],rep Q k⟩ := by rfl
private theorem bLeft (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨1,T++L,R⟩ = some ⟨1,L,T++R⟩ := by rfl
private theorem bRight (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨1,[false]++L,T++R⟩ = some ⟨1,[false]++P++L,R⟩ := by rfl
private theorem bEnd (v : Nat) (L : List Bool) : run0 (table v) 4 ⟨1,[false]++L,[true]⟩ = some ⟨0,[true]++P++L,[true]⟩ := by rfl
private theorem aLeft (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem aEnd (v : Nat) (R : List Bool) : run0 (table v) 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem bFinish (v a : Nat) (L : List Bool) :
    run0 (table v) (2*a+4) ⟨1,[false]++L,rep T a++[true]⟩ = some ⟨0,rep T (a+1)++[true]++L,[true]⟩ := by
  have h1 := sweepR (table v) 1 [false] [] T P 2 (bRight v) a L [true]
  simp only [List.nil_append] at h1
  have h2 := bEnd v (rep P a++L)
  have h := join0 h1 h2
  have hr : [true]++P++(rep P a++L) = rep T (a+1)++[true]++L := by
    calc
      _ = ([true]++rep P (a+1))++L := by simp only [rep,List.append_assoc]
      _ = _ := by rw [rot]
  rw [hr] at h
  exact h
private theorem aFinish (v m : Nat) : run0 (table v) (2*m) ⟨0,rep T m,[true]⟩ = some (family m) := by
  have h := sweepL (table v) 0 [] [] T Q 2 (aLeft v) m [] [true]
  simp only [List.nil_append,List.append_nil] at h
  simpa only [family,qrot] using h
private theorem aFinishOdd (v m : Nat) : run0 (table v) (2*m+2) ⟨0,rep T m++[true],[true]⟩ = some (family (m+1)) := by
  have h1 := sweepL (table v) 0 [] [] T Q 2 (aLeft v) m [true] [true]
  simp only [List.nil_append] at h1
  have h := join0 h1 (aEnd v (rep Q m++[true]))
  unfold family
  rw [qrot]
  simpa only [rep,List.append_assoc] using h
private theorem bLeftSweep (v a : Nat) (L : List Bool) :
    run0 (table v) (2*a) ⟨1,rep T a++L,[true]⟩ = some ⟨1,L,rep T a++[true]⟩ := by
  simpa only [List.nil_append] using sweepL (table v) 1 [] [] T T 2 (bLeft v) a L [true]
private theorem eRight (v : Nat) (hv : v=0 ∨ v=1 ∨ v=3) (L R : List Bool) :
    run0 (table v) 2 ⟨4,[true]++L,Q++R⟩ = some ⟨4,[true]++P++L,R⟩ := by
  rcases hv with rfl|rfl|rfl <;> rfl
private theorem eEnd (v : Nat) (hv : v=0 ∨ v=1 ∨ v=3) (L : List Bool) :
    run0 (table v) 2 ⟨4,[true]++L,[]⟩ = some ⟨1,[true]++L,[true]⟩ := by
  rcases hv with rfl|rfl|rfl <;> rfl
private theorem eSweep (v : Nat) (hv : v=0 ∨ v=1 ∨ v=3) (n : Nat) (L : List Bool) :
    run0 (table v) (2*n+2) ⟨4,[true]++L,rep Q n⟩ = some ⟨1,rep T n++[true]++L,[true]⟩ := by
  have h1 := sweepR (table v) 4 [true] [] Q P 2 (eRight v hv) n L []
  simp only [List.nil_append,List.append_nil] at h1
  have h := join0 h1 (eEnd v hv (rep P n++L))
  rw [← List.append_assoc [true] (rep P n) L,rot] at h
  exact h
private theorem eStart0 (n : Nat) : run0 (table 0) 2 ⟨4,[false,false],rep Q (n+1)⟩ = some ⟨4,[true,false,false,false],rep Q n⟩ := by rfl
private theorem eStart1 (n : Nat) : run0 (table 1) 2 ⟨4,[false,false],rep Q (n+1)⟩ = some ⟨4,[true,false,true,false],rep Q n⟩ := by rfl
private theorem eStart3 (n : Nat) : run0 (table 3) 4 ⟨4,[false,false],rep Q (n+1)⟩ = some ⟨4,[true,false,true,false],rep Q n⟩ := by rfl
private theorem bFinishEven (v a b : Nat) :
    run0 (table v) (2*a+4+2*(a+2+b)) ⟨1,[false,false]++rep T b,rep T a++[true]⟩ = some (family (a+2+b)) := by
  have h1 := bFinish v a ([false]++rep T b)
  have h1' : run0 (table v) (2*a+4) ⟨1,[false,false]++rep T b,rep T a++[true]⟩ = some ⟨0,rep T (a+2+b),[true]⟩ := by
    have h : rep T (a+1)++[true]++([false]++rep T b) = rep T (a+2+b) := by
      rw [List.append_assoc]
      change rep T (a+1)++rep T (b+1)=rep T (a+2+b)
      rw [rep_add,show a+1+(b+1)=a+2+b by omega]
    rw [h] at h1
    exact h1
  exact join0 h1' (aFinish v (a+2+b))
private theorem bFinishBlank (v a : Nat) :
    run0 (table v) (2*a+4+2*(a+1)+2) ⟨1,[],rep T a++[true]⟩ = some (family (a+2)) := by
  have h1 := bFinish v a []
  simp only [List.append_nil] at h1
  have h1' : run0 (table v) (2*a+4) ⟨1,[],rep T a++[true]⟩ = some ⟨0,rep T (a+1)++[true],[true]⟩ := by
    have he : run0 (table v) (2*a+4) ⟨1,[],rep T a++[true]⟩ = run0 (table v) (2*a+4) ⟨1,[false],rep T a++[true]⟩ := by
      rw [show 2*a+4=(2*a+3)+1 by omega]
      rfl
    exact he.trans h1
  have h := join0 h1' (aFinishOdd v (a+1))
  simpa only [Nat.add_assoc] using h

theorem growth0 (n : Nat) : run0 (table 0) (8*n+21) (family (n+1)) = some (family (n+3)) := by
  have h1 := join0 (startE 0 (n+1)) (eStart0 n)
  have h2 := eSweep 0 (Or.inl rfl) n [false,false,false]
  have h2' : run0 (table 0) (2*n+2) ⟨4,[true,false,false,false],rep Q n⟩ = some ⟨1,rep T (n+1)++[false,false],[true]⟩ := by
    have h : rep T n++[true]++[false,false,false] = rep T (n+1)++[false,false] := by
      rw [List.append_assoc]; change rep T n++(T++[false,false])=rep T (n+1)++[false,false]
      rw [← List.append_assoc]
      have hh := rep_add T n 1
      rw [show rep T n++T=rep T (n+1) from hh]
    rw [h] at h2; exact h2
  have h := join0 (join0 (join0 h1 h2') (bLeftSweep 0 (n+1) [false,false])) (bFinishEven 0 (n+1) 0)
  simpa only [rep,List.append_nil,Nat.add_zero,show 3+2+(2*n+2)+2*(n+1)+(2*(n+1)+4+2*(n+1+2+0))=8*n+21 by omega] using h
private theorem growth13 (v d n : Nat) (hv : v=1 ∨ v=3)
    (hs : run0 (table v) d ⟨4,[false,false],rep Q (n+1)⟩ = some ⟨4,[true,false,true,false],rep Q n⟩) :
    run0 (table v) (8*n+25+d) (family (n+1)) = some (family (n+4)) := by
  have h1 := join0 (startE v (n+1)) hs
  have h2 := eSweep v (Or.inr hv) n [false,true,false]
  have h2' : run0 (table v) (2*n+2) ⟨4,[true,false,true,false],rep Q n⟩ = some ⟨1,rep T (n+2),[true]⟩ := by
    have h : rep T n++[true]++[false,true,false] = rep T (n+2) := by
      rw [List.append_assoc]; change rep T n++rep T 2=rep T (n+2); exact rep_add T n 2
    rw [h] at h2; exact h2
  have h3 := bLeftSweep v (n+2) []
  simp only [List.append_nil] at h3
  have h := join0 (join0 (join0 h1 h2') h3) (bFinishBlank v (n+2))
  simpa only [show 3+d+(2*n+2)+2*(n+2)+(2*(n+2)+4+2*(n+2+1)+2)=8*n+25+d by omega,show n+2+2=n+4 by omega] using h

theorem growth1 (n : Nat) : run0 (table 1) (8*n+27) (family (n+1)) = some (family (n+4)) := by
  simpa only [show 8*n+25+2=8*n+27 by omega] using growth13 1 2 n (Or.inl rfl) (eStart1 n)
theorem growth3 (n : Nat) : run0 (table 3) (8*n+29) (family (n+1)) = some (family (n+4)) := by
  simpa only [show 8*n+25+4=8*n+29 by omega] using growth13 3 4 n (Or.inr rfl) (eStart3 n)
private theorem eRight24 (v : Nat) (hv : v=2 ∨ v=4) (L R : List Bool) :
    run0 (table v) 8 ⟨4,[false,false]++L,Q++Q++R⟩ = some ⟨4,[false,false]++T++L,Q++R⟩ := by
  rcases hv with rfl|rfl <;> rfl
private theorem eEnd24 (v : Nat) (hv : v=2 ∨ v=4) (L : List Bool) :
    run0 (table v) 10 ⟨4,[false,false]++L,Q⟩ = some ⟨1,[false,false]++T++L,T++[true]⟩ := by
  rcases hv with rfl|rfl <;> rfl
private theorem growth24 (v n : Nat) (hv : v=2 ∨ v=4) :
    run0 (table v) (10*n+27) (family (n+1)) = some (family (n+4)) := by
  have h1 := startE v (n+1)
  have h2 := sweepR (table v) 4 [false,false] Q Q T 8 (eRight24 v hv) n [] []
  simp only [List.append_nil] at h2
  have h3 := eEnd24 v hv (rep T n)
  have h := join0 (join0 (join0 h1 h2) h3) (bFinishEven v 1 (n+1))
  simpa only [rep,List.append_assoc,show 1+2+(n+1)=n+4 by omega,show 3+8*n+10+(2*1+4+2*(n+4))=10*n+27 by omega] using h

theorem growth2 (n : Nat) : run0 (table 2) (10*n+27) (family (n+1)) = some (family (n+4)) := growth24 2 n (Or.inl rfl)
theorem growth4 (n : Nat) : run0 (table 4) (10*n+27) (family (n+1)) = some (family (n+4)) := growth24 4 n (Or.inr rfl)

theorem first0 : run0 (table 0) 19 ⟨0,[],[]⟩ = some (family 3) := by rfl
theorem first1 : run0 (table 1) 19 ⟨0,[],[]⟩ = some (family 3) := by rfl
theorem first2 : run0 (table 2) 19 ⟨0,[],[]⟩ = some (family 3) := by rfl
theorem first3 : run0 (table 3) 19 ⟨0,[],[]⟩ = some (family 3) := by rfl
theorem first4 : run0 (table 4) 19 ⟨0,[],[]⟩ = some (family 3) := by rfl
def increment (v : Nat) : Nat := if v=0 then 2 else 3
def sweepCost (v n : Nat) : Nat :=
  if v=0 then 8*n+21 else if v=1 then 8*n+27 else if v=3 then 8*n+29 else 10*n+27

theorem growth (v n : Nat) (hv : v<5) :
    run0 (table v) (sweepCost v n) (family (n+1)) = some (family (n+1+increment v)) := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · simpa [sweepCost,increment,show n+1+2=n+3 by omega] using growth0 n
  · simpa [sweepCost,increment,show n+1+3=n+4 by omega] using growth1 n
  · simpa [sweepCost,increment,show n+1+3=n+4 by omega] using growth2 n
  · simpa [sweepCost,increment,show n+1+3=n+4 by omega] using growth3 n
  · simpa [sweepCost,increment,show n+1+3=n+4 by omega] using growth4 n

def orbit (v i : Nat) : Nat := 2+i*increment v

theorem orbit_first (v : Nat) (hv : v<5) :
    run0 (table v) 19 ⟨0,[],[]⟩ = some (family (orbit v 0+1)) := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl

theorem orbit_step (v i : Nat) (hv : v<5) :
    run0 (table v) (sweepCost v (orbit v i)) (family (orbit v i+1)) = some (family (orbit v (i+1)+1)) := by
  have h := growth v (orbit v i) hv
  have he : orbit v i+1+increment v=orbit v (i+1)+1 := by
    unfold orbit
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  simpa only [he] using h

theorem cost_pos (v n : Nat) : 0<sweepCost v n := by
  unfold sweepCost
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem never (v : Nat) (hv : v<5) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun i => family (orbit v i+1)) 19
    (fun i => sweepCost v (orbit v i)) (orbit_first v hv)
    (fun i => cost_pos v (orbit v i)) (fun i => orbit_step v i hv) m hm

#print axioms growth
#print axioms orbit_first
#print axioms orbit_step
#print axioms cost_pos
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0RE
