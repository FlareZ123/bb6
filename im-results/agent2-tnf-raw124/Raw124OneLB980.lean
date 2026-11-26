import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124OneLB980
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), some (some ⟨false,false,4⟩),
    some (some ⟨true,true,2⟩), some (some ⟨false,true,0⟩),
    some (some ⟨false,true,3⟩), none,
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,false,0⟩), some (some ⟨true,false,5⟩),
    some (some ⟨true,false,4⟩), some (some ⟨true,false,1⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none
private def P : List Bool := [true,false]
private def O : List Bool := [true,true]
private def Z : List Bool := [false,false]
private def S : List Bool := [false,true,false,true,false]
private def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
private def E (l r : List Bool) : Z0 := ⟨4,l,r⟩
private theorem rep_add (W : List Bool) (n m : Nat) : rep W (n+m) = rep W n ++ rep W m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega, rep, ih, rep, List.append_assoc]
private theorem scanOne (L R : List Bool) :
    run0 table 2 (A (Z++L) (P++R)) = some (A (Z++P++L) R) := by rfl
private theorem scan (n : Nat) (R : List Bool) :
    run0 table (2*(n+1)) (A [] (rep P (n+1)++R)) = some (A (Z++rep P n++[true]) R) := by
  have h1 : run0 table 2 (A [] (rep P (n+1)++R)) = some (A (Z++[true]) (rep P n++R)) := by rfl
  have h2 := sweepR table 0 Z [] P P 2 scanOne n [true] R
  simp only [List.nil_append] at h2
  have h := join0 h1 h2
  rw [show 2+2*n=2*(n+1) by omega] at h
  exact h
private theorem turn' (L : List Bool) :
    run0 table 20 (A (Z++true::L) []) = some (E (true::L) S) := by rfl
private theorem turnRep (n : Nat) :
    run0 table 20 (A (Z++rep P n++[true]) []) = some (E (rep P n++[true]) S) := by
  cases n with
  | zero => exact turn' []
  | succ n => simpa only [rep,P,List.append_assoc,List.cons_append,List.nil_append] using turn' (false::(rep P n++[true]))
private theorem unaryOne (L R : List Bool) :
    run0 table 2 (E (P++L) R) = some (E L (O++R)) := by rfl
private theorem unarySweep (n : Nat) :
    run0 table (2*n) (E (rep P n++[true]) S) = some (E [true] (rep O n++S)) := by
  simpa only [E,List.nil_append] using sweepL table 4 [] [] P O 2 unaryOne n [true] S
private theorem unaryEnd (R : List Bool) :
    run0 table 3 (E [true] R) = some (A [] ([true,true,true]++R)) := by rfl
private theorem toUnary (n : Nat) :
    run0 table (4*(n+1)+21) (A [] (rep P (n+1))) =
    some (A [] (rep O (n+1)++true::S)) := by
  have h1 := scan n []
  simp only [List.append_nil] at h1
  have h := join0 (join0 (join0 h1 (turnRep n)) (unarySweep n)) (unaryEnd (rep O n++S))
  rw [show 2*(n+1)+20+2*n+3=4*(n+1)+21 by omega] at h
  have he : [true,true,true]++(rep O n++S) = rep O (n+1)++true::S := by
    rw [rep, List.append_assoc]
    have hr : ∀ n, true::rep O n = rep O n++[true] := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp only [rep,List.append_assoc]; change true::true::true::rep O n = true::true::(rep O n++[true]); rw [ih]
    change true::true::(true::(rep O n++S)) = true::true::(rep O n++true::S)
    have hx : true::(rep O n++S) = rep O n++true::S := by
      calc
        true::(rep O n++S) = (true::rep O n)++S := rfl
        _ = (rep O n++[true])++S := by rw [hr]
        _ = rep O n++true::S := by rw [List.append_assoc]; rfl
    rw [hx]
  rw [he] at h
  exact h
private theorem popOne (L R : List Bool) :
    run0 table 2 (A (P++L) R) = some (A L (P++R)) := by rfl
private theorem pop (k : Nat) (R : List Bool) :
    run0 table (2*k) (A (rep P k++[true]) R) = some (A [true] (rep P k++R)) := by
  simpa only [A,List.nil_append] using sweepL table 0 [] [] P P 2 popOne k [true] R
private theorem popEnd (R : List Bool) :
    run0 table 2 (A [true] R) = some (A [] (P++R)) := by rfl
private theorem popAll (k : Nat) (R : List Bool) :
    run0 table (2*(k+1)) (A (rep P k++[true]) R) = some (A [] (rep P (k+1)++R)) := by
  have h := join0 (pop k R) (popEnd (rep P k++R))
  rw [show 2*k+2=2*(k+1) by omega] at h
  simpa only [rep,List.append_assoc] using h
private theorem consume (k : Nat) (R : List Bool) :
    run0 table (4*k+6) (A [] (rep P k++[true,true]++R)) =
    some (A [] (rep P (k+2)++R)) := by
  cases k with
  | zero =>
    have h1 : run0 table 2 (A [] ([true,true]++R)) = some (A (P++[true]) R) := by rfl
    have h := join0 h1 (popAll 1 R)
    exact h
  | succ k =>
    have h1 := scan k ([true,true]++R)
    have h2 : run0 table 2 (A (Z++rep P k++[true]) ([true,true]++R)) =
      some (A (rep P (k+2)++[true]) R) := by
      simp only [rep,List.append_assoc]; rfl
    have h := join0 (join0 h1 h2) (popAll (k+2) R)
    rw [show 2*(k+1)+2+2*(k+2+1)=4*(k+1)+6 by omega] at h
    simpa only [List.append_assoc] using h
private theorem consumeMany (k m : Nat) :
    run0 table (m*(4*k+6)+4*m*(m-1)) (A [] (rep P k++rep O m++true::S)) =
    some (A [] (rep P (k+2*m)++true::S)) := by
  induction m generalizing k with
  | zero => simp [rep,run0]
  | succ m ih =>
    have h1 := consume k (rep O m++true::S)
    have h2 := ih (k+2)
    simp only [List.append_assoc] at h1 h2
    have h := join0 h1 h2
    rw [show k+2+2*m=k+2*(m+1) by omega] at h
    have he : 4*k+6+(m*(4*(k+2)+6)+4*m*(m-1)) = (m+1)*(4*k+6)+4*(m+1)*m := by
      cases m with
      | zero => simp
      | succ m => simp only [Nat.succ_sub_one]; simp [Nat.add_mul,Nat.mul_add]; omega
    rw [he] at h
    simpa only [rep,O,List.append_assoc,Nat.add_sub_cancel] using h

def size : Nat → Nat
  | 0 => 3
  | k+1 => 2*size k+3
private theorem size_pos (k : Nat) : 0 < size k := by cases k <;> simp [size] <;> omega
def family (k : Nat) : Z0 := A [] (rep P (size k))
def cost (k : Nat) : Nat := 4*size k*size k+6*size k+21

theorem root : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have hpos := size_pos k
  obtain ⟨n,hn⟩ : ∃ n, size k = n+1 := ⟨size k-1,by omega⟩
  unfold family cost
  rw [size, hn]
  have h1 := toUnary n
  have h2 := consumeMany 0 (n+1)
  simp only [rep,List.nil_append,Nat.zero_add] at h2
  have h := join0 h1 h2
  have he : 4*(n+1)+21+((n+1)*(4*0+6)+4*(n+1)*((n+1)-1)) = 4*(n+1)*(n+1)+6*(n+1)+21 := by
    simp [Nat.add_mul,Nat.mul_add]; omega
  rw [he] at h
  have hf : rep P (2*(n+1))++true::S = rep P (2*(n+1)+3) := by rw [rep_add]; rfl
  rw [hf] at h
  exact h

theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 cost root (by intro k; unfold cost; omega) growth m hm
#print axioms root
#print axioms growth
#print axioms never_source
end BB6.Agent2Raw124OneLB980
