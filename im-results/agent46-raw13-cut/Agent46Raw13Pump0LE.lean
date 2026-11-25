import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0LE
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

private def T : List Bool := [true,false]
private def P : List Bool := [false,true]
private def Q : List Bool := [true,true]
private def E (z : List Bool) (a b : Nat) : Z0 := ⟨4,z,[false,false]++rep T a++rep Q b⟩
private def M (a b : Nat) : Z0 := ⟨1,[false]++T,rep T (a+1)++rep Q b⟩
private def B (z : List Bool) (c d : Nat) : Z0 := ⟨1,z,rep T c++rep Q d++[true]⟩

private theorem rotP (a : Nat) : [true]++rep P a=rep T a++[true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change T++([true]++rep P a)=T++(rep T a++[true])
    rw [ih]
private theorem rotPtail (a : Nat) (L : List Bool) :
    [true]++rep P a++L=rep T a++[true]++L := by
  rw [rotP]
private theorem commuteQ (a : Nat) : [true]++rep Q a=rep Q a++[true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change Q++([true]++rep Q a)=Q++(rep Q a++[true])
    rw [ih]
private theorem frame1 (a : Nat) :
    [true]++rep P a++[false,false,true,false]=rep T (a+1)++[false,true,false] := by
  rw [rotPtail,List.append_assoc]
  change rep T a ++ (T ++ [false,true,false]) = rep T (a+1)++[false,true,false]
  rw [← List.append_assoc,rep_snoc]
  rfl
private theorem frame2 (a : Nat) :
    [true]++rep P a++T=rep T a++[true,true,false] := by
  rw [rotPtail,List.append_assoc]
  rfl

private theorem eStart0 (z : List Bool) (hz : z=[] ∨ z=[false]) (b : Nat) :
    run0 table 4 (E z 0 (b+1)) = some ⟨1,T++[false,true,false],rep Q b⟩ := by
  rcases hz with rfl|rfl <;> rfl
private theorem eStartSucc (z : List Bool) (hz : z=[] ∨ z=[false]) (a b : Nat) :
    run0 table 4 (E z (a+1) (b+1)) = some ⟨1,[false,false,false,true,false],rep T a++rep Q (b+1)⟩ := by
  rcases hz with rfl|rfl <;> rfl
private theorem bRight (L R : List Bool) :
    run0 table 2 ⟨1,[false]++L,T++R⟩ = some ⟨1,[false]++P++L,R⟩ := by rfl
private theorem bRightQ (L R : List Bool) :
    run0 table 2 ⟨1,[false]++L,Q++R⟩ = some ⟨1,[true]++P++L,R⟩ := by rfl
private theorem bLeft (L R : List Bool) :
    run0 table 2 ⟨1,T++L,R⟩ = some ⟨1,L,T++R⟩ := by rfl
private theorem bLeftE (R : List Bool) :
    run0 table 2 ⟨1,[true,true,false],R⟩ = some ⟨4,[false],[false,false]++R⟩ := by rfl
private theorem bRightEnd (L : List Bool) :
    run0 table 2 ⟨1,[false]++L,[]⟩ = some ⟨0,[true]++L,[true]⟩ := by rfl
private theorem aLeft (L R : List Bool) :
    run0 table 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem aToB (R : List Bool) :
    run0 table 4 ⟨0,[true,true,false],R⟩ = some ⟨1,[false],T++R⟩ := by rfl
private theorem bLeftBlank (R : List Bool) :
    run0 table 2 ⟨1,[true],R⟩ = some ⟨1,[],T++R⟩ := by rfl
private theorem bRightSingle (L : List Bool) :
    run0 table 2 ⟨1,[false]++L,[true]⟩ = some ⟨1,[false]++P++L,[]⟩ := by rfl
private theorem aLeftBlank (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem aToE (R : List Bool) :
    run0 table 3 ⟨0,[],[true]++R⟩ = some ⟨4,[],[false,false]++R⟩ := by rfl

private theorem firstPass (z : List Bool) (hz : z=[] ∨ z=[false]) (a b : Nat) :
    run0 table (4*a+6) (E z a (b+1)) = some (M a b) := by
  cases a with
  | zero =>
    simpa only [M,rep,List.append_assoc,List.nil_append,Nat.zero_add,Nat.mul_zero] using join0 (eStart0 z hz b) (bLeft ([false]++T) (rep Q b))
  | succ a =>
    have h1 := eStartSucc z hz a b
    have h2 := sweepR table 1 [false] [] T P 2 bRight a [false,false,true,false] (rep Q (b+1))
    simp only [List.nil_append] at h2
    have h3 := bRightQ (rep P a++[false,false,true,false]) (rep Q b)
    have h3' : run0 table 2 ⟨1,[false]++rep P a++[false,false,true,false],rep Q (b+1)⟩ =
        some ⟨1,rep T (a+2)++[false,true,false],rep Q b⟩ := by
      have hh := frame1 (a+1)
      rw [← hh]
      simpa only [rep,List.append_assoc] using h3
    have h4 := sweepL table 1 [] [] T T 2 bLeft (a+2) [false,true,false] (rep Q b)
    simp only [List.nil_append] at h4
    have h := join0 (join0 (join0 h1 h2) h3') h4
    rw [show 4+2*a+2+2*(a+2)=4*(a+1)+6 by omega] at h
    exact h

private theorem secondPass (a b : Nat) :
    run0 table (4*a+10) (M a (b+1)) = some (E [false] (a+2) b) := by
  have h1 := sweepR table 1 [false] [] T P 2 bRight (a+1) T (rep Q (b+1))
  simp only [List.nil_append] at h1
  have h2 := bRightQ (rep P (a+1)++T) (rep Q b)
  have h2' : run0 table 2 ⟨1,[false]++rep P (a+1)++T,rep Q (b+1)⟩ =
      some ⟨1,rep T (a+2)++[true,true,false],rep Q b⟩ := by
    have hh := frame2 (a+2)
    rw [← hh]
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 1 [] [] T T 2 bLeft (a+2) [true,true,false] (rep Q b)
  simp only [List.nil_append] at h3
  have h4 := bLeftE (rep T (a+2)++rep Q b)
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 2*(a+1)+2+2*(a+2)+2=4*a+10 by omega] at h
  exact h

private theorem eStep (z : List Bool) (hz : z=[] ∨ z=[false]) (a b : Nat) :
    run0 table (8*a+16) (E z a (b+2)) = some (E [false] (a+2) b) := by
  have h := join0 (firstPass z hz a (b+1)) (secondPass a b)
  rw [show 4*a+6+(4*a+10)=8*a+16 by omega] at h
  exact h

private theorem eLast (z : List Bool) (hz : z=[] ∨ z=[false]) (a : Nat) :
    run0 table (8*a+16) (E z a 1) = some (B [false] 1 (a+1)) := by
  have h1 := firstPass z hz a 0
  have h2 := sweepR table 1 [false] [] T P 2 bRight (a+1) T []
  simp only [List.nil_append,List.append_nil] at h2
  have h2' : run0 table (2*(a+1)) (M a 0) =
      some ⟨1,[false]++rep P (a+1)++T,[]⟩ := by
    simpa only [M,rep,List.append_nil] using h2
  have h3 := bRightEnd (rep P (a+1)++T)
  have h3' : run0 table 2 ⟨1,[false]++rep P (a+1)++T,[]⟩ =
      some ⟨0,rep T (a+1)++[true,true,false],[true]⟩ := by
    rw [← frame2]
    simpa only [List.append_assoc] using h3
  have h4 := sweepL table 0 [] [] T Q 2 aLeft (a+1) [true,true,false] [true]
  simp only [List.nil_append] at h4
  have h5 := aToB (rep Q (a+1)++[true])
  have h := join0 (join0 (join0 (join0 h1 h2') h3') h4) h5
  rw [show 4*a+6+2*(a+1)+2+2*(a+1)+4=8*a+16 by omega] at h
  exact h

private theorem bStep0 (c d : Nat) :
    run0 table (4*c+6) (B [false] c (d+1)) = some (B [] (c+2) d) := by
  have h1 := sweepR table 1 [false] [] T P 2 bRight c [] (rep Q (d+1)++[true])
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := bRightQ (rep P c) (rep Q d++[true])
  have h2' : run0 table 2 ⟨1,[false]++rep P c,rep Q (d+1)++[true]⟩ =
      some ⟨1,rep T (c+1)++[true],rep Q d++[true]⟩ := by
    have hh := rotP (c+1)
    rw [← hh]
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 1 [] [] T T 2 bLeft (c+1) [true] (rep Q d++[true])
  simp only [List.nil_append] at h3
  have h4 := bLeftBlank (rep T (c+1)++(rep Q d++[true]))
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 2*c+2+2*(c+1)+2=4*c+6 by omega] at h
  simpa only [B,rep,List.append_assoc] using h

private theorem bStep (z : List Bool) (hz : z=[] ∨ z=[false]) (c d : Nat) :
    run0 table (4*c+6) (B z c (d+1)) = some (B [] (c+2) d) := by
  rcases hz with rfl|rfl
  · have h := bStep0 c d
    exact h
  · exact bStep0 c d

private theorem bLast0 (c : Nat) :
    run0 table (4*c+11) (B [false] c 0) = some (E [] 0 (c+2)) := by
  have h1 := sweepR table 1 [false] [] T P 2 bRight c [] [true]
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := bRightSingle (rep P c)
  have h3 := bRightEnd (rep P (c+1))
  rw [rotP] at h3
  have h3' : run0 table 2 ⟨1,[false]++P++rep P c,[]⟩ =
      some ⟨0,rep T (c+1)++[true],[true]⟩ := by
    exact h3
  have h4 := sweepL table 0 [] [] T Q 2 aLeft (c+1) [true] [true]
  simp only [List.nil_append] at h4
  have h5 := aLeftBlank (rep Q (c+1)++[true])
  have h5' : run0 table 2 ⟨0,[true],rep Q (c+1)++[true]⟩ =
      some ⟨0,[],[true]++rep Q (c+2)⟩ := by
    rw [commuteQ]
    exact h5
  have h6 := aToE (rep Q (c+2))
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3') h4) h5') h6
  rw [show 2*c+2+2+2*(c+1)+2+3=4*c+11 by omega] at h
  simpa only [B,E,rep,List.nil_append,List.append_nil] using h

private theorem bLast (z : List Bool) (hz : z=[] ∨ z=[false]) (c : Nat) :
    run0 table (4*c+11) (B z c 0) = some (E [] 0 (c+2)) := by
  rcases hz with rfl|rfl
  · exact bLast0 c
  · exact bLast0 c

private def costE (a : Nat) : Nat → Nat
  | 0 => 8*a+16
  | k+1 => 8*a+16+costE (a+2) k
private theorem eIter (z : List Bool) (hz : z=[] ∨ z=[false]) (a k : Nat) :
    run0 table (costE a k) (E z a (2*k+1)) = some (B [false] 1 (a+2*k+1)) := by
  induction k generalizing a z with
  | zero => simpa only [costE,Nat.mul_zero,Nat.add_zero] using eLast z hz a
  | succ k ih =>
    have h := join0 (eStep z hz a (2*k+1)) (ih [false] (Or.inr rfl) (a+2))
    simpa only [costE,show 2*(k+1)+1=2*k+1+2 by omega,show a+2+2*k+1=a+2*(k+1)+1 by omega] using h
private def costB (c : Nat) : Nat → Nat
  | 0 => 4*c+11
  | d+1 => 4*c+6+costB (c+2) d
private theorem bIter (z : List Bool) (hz : z=[] ∨ z=[false]) (c d : Nat) :
    run0 table (costB c d) (B z c d) = some (E [] 0 (c+2*d+2)) := by
  induction d generalizing c z with
  | zero => simpa only [costB,Nat.mul_zero,Nat.add_zero] using bLast z hz c
  | succ d ih =>
    have h := join0 (bStep z hz c d) (ih [] (Or.inl rfl) (c+2))
    simpa only [costB,show c+2+2*d+2=c+2*(d+1)+2 by omega] using h

def family (k : Nat) : Z0 := E [] 0 (2*k+1)
def cost (k : Nat) : Nat := costE 0 k+costB 1 (2*k+1)
theorem first : run0 table 22 ⟨0,[],[]⟩ = some (family 1) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (2*k+2)) := by
  have hE := eIter [] (Or.inl rfl) 0 k
  simp only [Nat.zero_add] at hE
  have h := join0 hE (bIter [false] (Or.inr rfl) 1 (2*k+1))
  simpa only [family,cost,Nat.zero_add,show 1+2*(2*k+1)+2=2*(2*k+2)+1 by omega] using h
private theorem costE_pos (a k : Nat) : 0 < costE a k := by
  cases k <;> simp only [costE] <;> omega
theorem cost_pos (k : Nat) : 0 < cost k := by
  have h := costE_pos 0 k
  unfold cost
  omega
private theorem costE_eq (a k : Nat) :
    costE a k=(k+1)*(8*a+16)+8*k*(k+1) := by
  induction k generalizing a with
  | zero => simp [costE]
  | succ k ih =>
    rw [costE,ih]
    simp only [Nat.mul_add,Nat.add_mul]
    omega
private theorem costB_eq (c d : Nat) :
    costB c d=4*d*d+(4*c+2)*d+4*(c+2*d)+11 := by
  induction d generalizing c with
  | zero => simp [costB]
  | succ d ih =>
    rw [costB,ih]
    simp only [Nat.mul_add,Nat.add_mul]
    omega
theorem cost_closed (k : Nat) : cost k=24*k*k+68*k+49 := by
  rw [cost,costE_eq,costB_eq]
  simp only [Nat.mul_add,Nat.add_mul]
  rw [show 4*(2*k)*(2*k)=16*(k*k) by
    calc
      _ = (4*2*2)*(k*k) := by ac_rfl
      _ = _ := by rfl]
  simp only [Nat.mul_assoc]
  omega
private def orbit : Nat → Nat
  | 0 => 1
  | i+1 => 2*orbit i+2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun i => family (orbit i)) 22 (fun i => cost (orbit i)) first
    (fun i => cost_pos (orbit i)) (fun i => growth (orbit i)) m hm

#print axioms never
#print axioms growth
#print axioms cost_closed
#print axioms cost_pos
end BB6Coverage.Agent31Pump.Raw13Pump0LE
