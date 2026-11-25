import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump1RE2
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
private def T : List Bool := [true,false]
private def P : List Bool := [false,true]
private def Q : List Bool := [true,true]
private def E (a b : Nat) : Z0 := ⟨4,P,rep T a++rep Q b⟩
private def B (a b : Nat) : Z0 := ⟨1,[],rep T a++rep Q b++[true]⟩
private def A (k : Nat) : Z0 := ⟨0,[],rep Q k++[true]⟩
private theorem rotP (a : Nat) : [true]++rep P a=rep T a++[true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change T++([true]++rep P a)=T++(rep T a++[true])
    rw [ih]
private theorem commuteQ (a : Nat) : [true]++rep Q a=rep Q a++[true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change Q++([true]++rep Q a)=Q++(rep Q a++[true])
    rw [ih]
private theorem aStart (k : Nat) : run0 table 3 (A (k+1)) = some (E 0 (k+1)) := by
  unfold A E
  simp only [rep,List.nil_append,List.append_assoc]
  rw [← commuteQ k]
  rfl
private theorem eRight (L R : List Bool) :
    run0 table 2 ⟨4,[false]++L,T++R⟩ = some ⟨4,[false]++P++L,R⟩ := by rfl
private theorem eRightQ (L R : List Bool) :
    run0 table 2 ⟨4,[false]++L,Q++R⟩ = some ⟨4,[true]++P++L,R⟩ := by rfl
private theorem eToB (L R : List Bool) :
    run0 table 2 ⟨4,[true]++L,Q++R⟩ = some ⟨1,T++[true]++L,R⟩ := by rfl
private theorem bLeft (L R : List Bool) :
    run0 table 2 ⟨1,T++L,R⟩ = some ⟨1,L,T++R⟩ := by rfl
private theorem bToE (R : List Bool) :
    run0 table 2 ⟨1,Q,R⟩ = some ⟨4,P,R⟩ := by rfl
private theorem eToA (L : List Bool) :
    run0 table 2 ⟨4,[true]++L,[]⟩ = some ⟨0,[true]++L,[true]⟩ := by rfl
private theorem aLeft (L R : List Bool) :
    run0 table 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem aToB (R : List Bool) :
    run0 table 4 ⟨0,Q,[true]++R⟩ = some ⟨1,[],T++[true]++R⟩ := by rfl
private theorem eScan (a b : Nat) :
    run0 table (2*a+2) (E a (b+1)) = some ⟨4,rep T (a+1)++Q,rep Q b⟩ := by
  have h1 := sweepR table 4 [false] [] T P 2 eRight a [true] (rep Q (b+1))
  have h2 := eRightQ (rep P a++[true]) (rep Q b)
  simp only [List.nil_append] at h1
  have h := join0 h1 h2
  unfold E
  simp only [rep,List.nil_append,List.append_assoc] at h ⊢
  have hh : [true]++(P++(rep P a++[true])) = T++(rep T a++Q) := by
    change T++([true]++rep P a++[true]) = T++(rep T a++Q)
    rw [rotP]
    simp only [List.append_assoc]
    rfl
  rw [hh] at h
  exact h
private theorem eStep (a b : Nat) :
    run0 table (4*a+10) (E a (b+2)) = some (E (a+2) b) := by
  have h1 := eScan a (b+1)
  have h2 := eToB (rep P (a+1)++[true]) (rep Q b)
  have hh : [true]++(rep P (a+1)++[true]) = rep T (a+1)++Q := by
    rw [← List.append_assoc,rotP,List.append_assoc]
    rfl
  rw [hh, List.append_assoc T [true],hh] at h2
  have h2' : run0 table 2 ⟨4,rep T (a+1)++Q,rep Q (b+1)⟩ =
      some ⟨1,rep T (a+2)++Q,rep Q b⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 1 [] [] T T 2 bLeft (a+2) Q (rep Q b)
  simp only [List.nil_append] at h3
  have h4 := bToE (rep T (a+2)++rep Q b)
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 2*a+2+2+2*(a+2)+2=4*a+10 by omega] at h
  exact h
private theorem eLast (a : Nat) :
    run0 table (4*a+10) (E a 1) = some (B 1 (a+1)) := by
  have h1 := eScan a 0
  have h2 := eToA (rep P (a+1)++[true])
  have hh : [true]++(rep P (a+1)++[true]) = rep T (a+1)++Q := by
    rw [← List.append_assoc,rotP,List.append_assoc]
    rfl
  rw [hh] at h2
  have h3 := sweepL table 0 [] [] T Q 2 aLeft (a+1) Q [true]
  simp only [List.nil_append] at h3
  have h4 := aToB (rep Q (a+1))
  rw [commuteQ] at h4
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2*a+2+2+2*(a+1)+4=4*a+10 by omega] at h
  change run0 table (4*a+10) (E a 1) = some ⟨1,[],T++(rep Q (a+1)++[true])⟩
  rw [← commuteQ (a+1)]
  simpa only [List.append_assoc] using h
private theorem bRight (L R : List Bool) :
    run0 table 2 ⟨1,[false]++L,T++R⟩ = some ⟨1,[false]++P++L,R⟩ := by rfl
private theorem bRightQ (L R : List Bool) :
    run0 table 2 ⟨1,[false]++L,Q++R⟩ = some ⟨1,[true]++P++L,R⟩ := by rfl
private theorem bRightSingle (L : List Bool) :
    run0 table 2 ⟨1,[false]++L,[true]⟩ = some ⟨1,[false]++P++L,[]⟩ := by rfl
private theorem bEnd (R : List Bool) :
    run0 table 2 ⟨1,[true],R⟩ = some ⟨1,[],T++R⟩ := by rfl
private theorem bToA (L : List Bool) :
    run0 table 2 ⟨1,[false]++L,[]⟩ = some ⟨0,[true]++L,[true]⟩ := by rfl
private theorem aEnd (R : List Bool) :
    run0 table 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem bZeroFrame (n : Nat) (R : List Bool) (hn : 0<n) :
    run0 table n ⟨1,[],R⟩ = run0 table n ⟨1,[false],R⟩ := by
  cases n with
  | zero => omega
  | succ n => rfl
private theorem bStepFrame (a b : Nat) :
    run0 table (4*a+6) ⟨1,[false],rep T a++rep Q (b+1)++[true]⟩ = some (B (a+2) b) := by
  have h1 := sweepR table 1 [false] [] T P 2 bRight a [] (rep Q (b+1)++[true])
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := bRightQ (rep P a) (rep Q b++[true])
  have h2' : run0 table 2 ⟨1,[false]++rep P a,rep Q (b+1)++[true]⟩ =
      some ⟨1,rep T (a+1)++[true],rep Q b++[true]⟩ := by
    rw [← rotP]
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 1 [] [] T T 2 bLeft (a+1) [true] (rep Q b++[true])
  simp only [List.nil_append] at h3
  have h4 := bEnd (rep T (a+1)++(rep Q b++[true]))
  have h := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 2*a+2+2*(a+1)+2=4*a+6 by omega] at h
  simpa only [B,rep,List.append_assoc] using h
private theorem bStep (a b : Nat) :
    run0 table (4*a+6) (B a (b+1)) = some (B (a+2) b) := by
  unfold B at ⊢
  rw [bZeroFrame _ _ (by omega)]
  exact bStepFrame a b
private theorem bLastFrame (a : Nat) :
    run0 table (4*a+8) ⟨1,[false],rep T a++[true]⟩ = some (A (a+2)) := by
  have h1 := sweepR table 1 [false] [] T P 2 bRight a [] [true]
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := bRightSingle (rep P a)
  have h3 := bToA (rep P (a+1))
  rw [rotP] at h3
  have h3' : run0 table 2 ⟨1,[false]++P++rep P a,[]⟩ =
      some ⟨0,rep T (a+1)++[true],[true]⟩ := by exact h3
  have h4 := sweepL table 0 [] [] T Q 2 aLeft (a+1) [true] [true]
  simp only [List.nil_append] at h4
  have h5 := aEnd (rep Q (a+1)++[true])
  have h := join0 (join0 (join0 (join0 h1 h2) h3') h4) h5
  rw [show 2*a+2+2+2*(a+1)+2=4*a+8 by omega] at h
  simpa only [A,rep,List.append_assoc] using h
private theorem bLast (a : Nat) : run0 table (4*a+8) (B a 0) = some (A (a+2)) := by
  unfold B
  simp only [rep,List.append_nil]
  rw [bZeroFrame _ _ (by omega)]
  exact bLastFrame a
private def costE (a : Nat) : Nat → Nat
  | 0 => 4*a+10
  | k+1 => 4*a+10+costE (a+2) k
private theorem eIter (a k : Nat) :
    run0 table (costE a k) (E a (2*k+1)) = some (B 1 (a+2*k+1)) := by
  induction k generalizing a with
  | zero => simpa only [costE,Nat.mul_zero,Nat.add_zero] using eLast a
  | succ k ih =>
    have h := join0 (eStep a (2*k+1)) (ih (a+2))
    simpa only [costE,show 2*(k+1)+1=2*k+1+2 by omega,show a+2+2*k+1=a+2*(k+1)+1 by omega] using h
private def costB (a : Nat) : Nat → Nat
  | 0 => 4*a+8
  | b+1 => 4*a+6+costB (a+2) b
private theorem bIter (a b : Nat) : run0 table (costB a b) (B a b) = some (A (a+2*b+2)) := by
  induction b generalizing a with
  | zero => simpa only [costB,Nat.mul_zero,Nat.add_zero] using bLast a
  | succ b ih =>
    have h := join0 (bStep a b) (ih (a+2))
    simpa only [costB,show a+2+2*b+2=a+2*(b+1)+2 by omega] using h

def family (k : Nat) : Z0 := A (2*k+1)
def cost (k : Nat) : Nat := 3+costE 0 k+costB 1 (2*k+1)
theorem first : run0 table 19 ⟨0,[],[]⟩ = some (family 1) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (2*k+2)) := by
  have h0 := aStart (2*k)
  have h1 := eIter 0 k
  simp only [Nat.zero_add] at h1
  have h := join0 (join0 h0 h1) (bIter 1 (2*k+1))
  simpa only [family,cost,show 1+2*(2*k+1)+2=2*(2*k+2)+1 by omega] using h
private theorem costE_pos (a k : Nat) : 0 < costE a k := by
  cases k <;> simp only [costE] <;> omega
theorem cost_pos (k : Nat) : 0 < cost k := by unfold cost; omega
private theorem costE_eq (a k : Nat) : costE a k=(k+1)*(4*a+10)+4*k*(k+1) := by
  induction k generalizing a with
  | zero => simp [costE]
  | succ k ih => rw [costE,ih]; simp only [Nat.mul_add,Nat.add_mul]; omega
private theorem costB_eq (a b : Nat) : costB a b=4*b*b+(4*a+2)*b+4*(a+2*b)+8 := by
  induction b generalizing a with
  | zero => simp [costB]
  | succ b ih => rw [costB,ih]; simp only [Nat.mul_add,Nat.add_mul]; omega
theorem cost_closed (k : Nat) : cost k=20*k*k+58*k+43 := by
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
  never_of_growth table (fun i => family (orbit i)) 19 (fun i => cost (orbit i)) first
    (fun i => cost_pos (orbit i)) (fun i => growth (orbit i)) m hm

#print axioms never
#print axioms growth
#print axioms cost_closed
#print axioms cost_pos
end BB6Coverage.Agent31Pump.Raw13Pump1RE2
