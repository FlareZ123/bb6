import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw124ZeroLF1RE.M42
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨true,false,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,true,4⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def T : List Bool := [true,true]
def R0 : List Bool := [false,true,false,true,true]

theorem startR (R : List Bool) :
    run0 table 2 ⟨0,[],P++R⟩ = some ⟨0,[false]++Q,R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 2 ⟨0,[false]++L,P++R⟩ = some ⟨0,[false]++Q++L,R⟩ := by rfl

theorem rightAll (n : Nat) (R : List Bool) :
    run0 table (2+2*n) ⟨0,[],rep P (n+1)++R⟩ = some ⟨0,[false]++rep Q (n+1),R⟩ := by
  have h1 := startR (rep P n++R)
  have h2 := sweepR table 0 [false] [] P Q 2 (by intro L R; exact rightOne L R) n Q R
  have h := join0 h1 (by simpa only [List.nil_append,List.append_assoc] using h2)
  simpa only [rep,List.append_assoc,rep_snoc Q n] using h

theorem firstTurn (L : List Bool) :
    run0 table 2 ⟨0,[false]++L,T⟩ = some ⟨0,[true,false,true]++L,[]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 2 ⟨0,P++L,R⟩ = some ⟨0,L,P++R⟩ := by rfl

theorem leftAll (n : Nat) :
    run0 table (2*n) ⟨0,rep P n++[true],[]⟩ = some ⟨0,[true],rep P n⟩ := by
  simpa only [List.nil_append,List.append_nil] using sweepL table 0 [] [] P P 2
    (by intro L R; exact leftOne L R) n [true] []

theorem finishFirst (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],P++R⟩ := by rfl

theorem turnSecond (L : List Bool) :
    run0 table 12 ⟨0,[false]++Q++L,[]⟩ = some ⟨4,[true]++L,R0⟩ := by rfl

theorem leftTwo (L R : List Bool) :
    run0 table 8 ⟨4,P++P++L,R⟩ = some ⟨4,L,Q++Q++R⟩ := by rfl

theorem finishSecond (R : List Bool) :
    run0 table 9 ⟨4,[true,false,true],R⟩ = some ⟨0,[],[true,false,true,false,true]++R⟩ := by rfl

theorem rep_add' (W : List Bool) (n m : Nat) : rep W (n+m) = rep W n ++ rep W m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem rep_double (W : List Bool) (n : Nat) : rep (W++W) n = rep W (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2+2*n by omega,rep_add' W 2 (2*n)]; simp only [rep,ih,List.append_assoc,List.append_nil]

theorem rot (n : Nat) : [true]++rep Q n = rep P n++[true] := by
  exact rotate true [false] n

theorem phase1 (n : Nat) : ∃ t, 0<t ∧
    run0 table t ⟨0,[],rep P (n+1)++T⟩ = some ⟨0,[],rep P (n+3)⟩ := by
  have h1 := rightAll n T
  have h2 := firstTurn (rep Q (n+1))
  have he : [true,false,true]++rep Q (n+1) = rep P (n+2)++[true] := by
    change P++[true]++rep Q (n+1) = _
    rw [List.append_assoc,rot]
    simp only [rep,List.append_assoc]
  rw [he] at h2
  have h3 := leftAll (n+2)
  have h4 := finishFirst (rep P (n+2))
  have h := join0 (join0 (join0 h1 h2) h3) h4
  exact ⟨2+2*n+2+2*(n+2)+2,by omega,by simpa only [rep] using h⟩

theorem phase2 (n : Nat) : ∃ t, 0<t ∧
    run0 table t ⟨0,[],rep P (2*n+4)⟩ = some ⟨0,[],rep P (2*n+6)++T⟩ := by
  have h1 := rightAll (2*n+3) []
  simp only [List.append_nil] at h1
  have h2 := turnSecond (rep Q (2*n+3))
  rw [rot] at h2
  have he : rep P (2*n+3)++[true] = rep (P++P) (n+1)++[true,false,true] := by
    rw [rep_double,show 2*n+3=2*(n+1)+1 by omega,rep_add']
    simp [rep,P,List.append_assoc]
  rw [he] at h2
  have h3 := sweepL table 4 [] [] (P++P) (Q++Q) 8 (by intro L R; exact leftTwo L R) (n+1) [true,false,true] R0
  simp only [List.nil_append] at h3
  have h4 := finishSecond (rep (Q++Q) (n+1)++R0)
  have he2 : [true,false,true,false,true]++(rep (Q++Q) (n+1)++R0) = rep P (2*n+6)++T := by
    rw [rep_double]
    change rep P 2++[true]++(rep Q (2*(n+1))++(rep Q 2++[true])) = _
    simp only [List.append_assoc]
    rw [← List.append_assoc (rep Q (2*(n+1))) (rep Q 2) [true],← rep_add']
    rw [← List.append_assoc [true] (rep Q (2*(n+1)+2)) [true],rot]
    simp only [List.append_assoc]
    rw [← List.append_assoc (rep P 2) (rep P (2*(n+1)+2)) ([true]++[true]),← rep_add']
    rw [show 2+ (2*(n+1)+2)=2*n+6 by omega]
    rfl
  rw [he2] at h4
  have H1 : run0 table (2+2*(2*n+3)) ⟨0,[],rep P (2*n+4)⟩ = some ⟨0,[false]++Q++rep Q (2*n+3),[]⟩ := by
    simpa only [rep,List.append_assoc] using h1
  exact ⟨_,by omega,join0 (join0 (join0 H1 h2) h3) h4⟩

theorem grow (n : Nat) : ∃ t, 0<t ∧
    run0 table t ⟨0,[],rep P (2*n+2)++T⟩ = some ⟨0,[],rep P (2*(n+2)+2)++T⟩ := by
  obtain ⟨t,ht,h1⟩ := phase1 (2*n+1)
  obtain ⟨u,hu,h2⟩ := phase2 n
  have h : 2*n+1+3=2*n+4 := by omega
  rw [h] at h1
  have H := join0 h1 h2
  rw [show 2*(n+2)+2=2*n+6 by omega]
  exact ⟨_,by omega,H⟩

theorem arbitrary (k : Nat) : ∃ t z, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t n, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some ⟨0,[],rep P (2*n+2)++T⟩ := by
    intro k
    induction k with
    | zero => exact ⟨13,0,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,n,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow n
      exact ⟨t+u,n+2,by omega,join0 h1 h2⟩
  obtain ⟨t,n,ht,h⟩ := aux k
  exact ⟨t,_,ht,h⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm

#print axioms never

end BB6.Agent4Raw124ZeroLF1RE.M42
