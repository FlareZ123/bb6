import Agent46CarryPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0RD
open BB6Coverage Agent31Pump

def table (v : Nat) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,true,3⟩)
  | 3,true => some (some ⟨true,decide (2≤v),4⟩)
  | 4,false => some (some (if v=0 then ⟨false,false,5⟩ else if v=1 then ⟨true,true,3⟩ else if v=2 then ⟨false,true,5⟩ else ⟨false,true,1⟩))
  | 4,true => if v=0 ∨ v=2 then none else some (some (if v=1 then ⟨false,false,5⟩ else ⟨false,true,5⟩))
  | 5,false => if 3≤v then none else some (some (if v=0 then ⟨true,true,3⟩ else if v=1 then ⟨false,false,4⟩ else ⟨false,false,2⟩))
  | 5,true => if v=1 then none else some (some (if v=0 then ⟨false,false,4⟩ else if v=2 then ⟨false,true,5⟩ else if v=3 then ⟨true,true,4⟩ else ⟨true,false,3⟩))
  | _,_ => none

def ZZ : List Bool := [false,false]
def Q : List Bool := [true,true]
def R0 (k : Nat) : List Bool := rep ZZ k++[true]
def R1 (k : Nat) : List Bool := rep Q k++[true,false]
def M0 : List Bool := [false,true]
def M1 : List Bool := [true,false]

private theorem dRight (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨3,[false]++L,ZZ++R⟩ = some ⟨3,[false]++ZZ++L,R⟩ := by rfl
private theorem dEnd (v : Nat) (hv : v=0 ∨ v=1) (L : List Bool) : run0 (table v) 2 ⟨3,[false]++L,[true]⟩ = some ⟨4,[false]++L,[true]⟩ := by rcases hv with rfl|rfl <;> rfl
private theorem dScan (v : Nat) (hv : v=0 ∨ v=1) (k : Nat) (L : List Bool) :
    run0 (table v) (2*k+2) ⟨3,[false]++L,R0 k⟩ = some ⟨4,rep ZZ k++([false]++L),[true]⟩ := by
  have h := sweepR (table v) 3 [false] [] ZZ ZZ 2 (dRight v) k L [true]
  simp only [List.nil_append] at h
  have h' := join0 h (dEnd v hv (rep ZZ k++L))
  have hr : [false]++(rep ZZ k++L) = rep ZZ k++([false]++L) := by
    rw [← List.append_assoc,show [false]++rep ZZ k=rep ZZ k++[false] from rotate false [false] k,List.append_assoc]
  rw [hr] at h'
  exact h'

private theorem start0 (k : Nat) (L : List Bool) : run0 (table 0) 2 ⟨4,ZZ++L,R0 k⟩ = some ⟨3,[false,true]++L,R0 k⟩ := by rfl
private theorem start0blank (k : Nat) : run0 (table 0) 2 ⟨4,[],R0 k⟩ = some ⟨3,[false,true],R0 k⟩ := by rfl
private theorem prepare0 (k : Nat) (L : List Bool) : run0 (table 0) (2*k+4) ⟨4,ZZ++L,R0 k⟩ = some ⟨4,rep ZZ k++(M0++L),R0 0⟩ := by
  have h := join0 (start0 k L) (dScan 0 (Or.inl rfl) k ([true]++L))
  rw [show 2+(2*k+2)=2*k+4 by omega] at h
  exact h
private theorem prepare0blank (k : Nat) : run0 (table 0) (2*k+4) ⟨4,[],R0 k⟩ = some ⟨4,rep ZZ k++M0,R0 0⟩ := by
  have h := join0 (start0blank k) (dScan 0 (Or.inl rfl) k [true])
  rw [show 2+(2*k+2)=2*k+4 by omega] at h
  exact h
private theorem finish0 (k : Nat) (L : List Bool) : run0 (table 0) 2 ⟨4,M0++L,R0 k⟩ = some ⟨4,L,R0 (k+1)⟩ := by rfl
private theorem finish0blank (k : Nat) : run0 (table 0) 2 ⟨4,M0,R0 k⟩ = some ⟨4,[],R0 (k+1)⟩ := by rfl

private theorem start1 (k : Nat) (L : List Bool) : run0 (table 1) 2 ⟨4,[false]++L,R0 (k+1)⟩ = some ⟨3,[false,false,true]++L,R0 k⟩ := by rfl
private theorem prepare1general (k : Nat) (L : List Bool) : run0 (table 1) (2*k+2) ⟨4,[false]++L,R0 k⟩ = some ⟨4,rep ZZ k++([true]++L),R0 0⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    have h := join0 (start1 k L) (dScan 1 (Or.inr rfl) k ([false,true]++L))
    have he : rep ZZ k++([false]++([false,true]++L)) = rep ZZ (k+1)++([true]++L) := by
      rw [rep,← rep_snoc ZZ k,List.append_assoc]
      rfl
    rw [he] at h
    simpa only [show 2+(2*k+2)=2*(k+1)+2 by omega,show R0 0=[true] by rfl] using h
private theorem prepare1 (k : Nat) (L : List Bool) : run0 (table 1) (2*k+2) ⟨4,ZZ++L,R0 k⟩ = some ⟨4,rep ZZ k++(M1++L),R0 0⟩ := by
  exact prepare1general k ([false]++L)
private theorem prepare1blank (k : Nat) : run0 (table 1) (2*k+2) ⟨4,[],R0 k⟩ = some ⟨4,rep ZZ k++[true],R0 0⟩ := by
  have he : run0 (table 1) (2*k+2) ⟨4,[],R0 k⟩ = run0 (table 1) (2*k+2) ⟨4,[false],R0 k⟩ := by
    rw [show 2*k+2=(2*k+1)+1 by omega]; rfl
  exact he.trans (prepare1general k [])
private theorem finish1 (k : Nat) (L : List Bool) : run0 (table 1) 2 ⟨4,M1++L,R0 k⟩ = some ⟨4,L,R0 (k+1)⟩ := by rfl
private theorem finish1blank (k : Nat) : run0 (table 1) 2 ⟨4,[true],R0 k⟩ = some ⟨4,[],R0 (k+1)⟩ := by rfl

private theorem start2 (k : Nat) (L : List Bool) : run0 (table 2) 5 ⟨0,[false]++L,R1 (k+1)⟩ = some ⟨5,[true,false,false,true]++L,rep Q k++[false]⟩ := by
  have h : R1 (k+1) = [true,true,true]++(rep Q k++[false]) := by
    unfold R1
    rw [rep,List.append_assoc]
    have hr : rep Q k++[true,false] = [true]++(rep Q k++[false]) := by
      have hq : [true]++rep Q k=rep Q k++[true] := rotate true [true] k
      rw [← List.append_assoc [true] (rep Q k),hq,List.append_assoc]
      rfl
    rw [hr]
    rfl
  rw [h]
  rfl
private theorem fRight (L R : List Bool) : run0 (table 2) 2 ⟨5,[true]++L,Q++R⟩ = some ⟨5,[true]++ZZ++L,R⟩ := by rfl
private theorem fEnd (L : List Bool) : run0 (table 2) 3 ⟨5,[true]++L,[false]⟩ = some ⟨0,L,[true,false]⟩ := by rfl
private theorem prepare2general (k : Nat) (L : List Bool) : run0 (table 2) (2*k+6) ⟨0,[false]++L,R1 k⟩ = some ⟨0,rep ZZ k++([true]++L),R1 0⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    have h0 := start2 k L
    have h1 := sweepR (table 2) 5 [true] [] Q ZZ 2 fRight k ([false,false,true]++L) [false]
    simp only [List.nil_append] at h1
    have h := join0 (join0 h0 h1) (fEnd (rep ZZ k++([false,false,true]++L)))
    have he : rep ZZ k++([false,false,true]++L) = rep ZZ (k+1)++([true]++L) := by
      rw [rep,← rep_snoc ZZ k,List.append_assoc]
      rfl
    rw [he] at h
    simpa only [show 5+2*k+3=2*(k+1)+6 by omega,show R1 0=[true,false] by rfl] using h
private theorem prepare2 (k : Nat) (L : List Bool) : run0 (table 2) (2*k+6) ⟨0,ZZ++L,R1 k⟩ = some ⟨0,rep ZZ k++(M1++L),R1 0⟩ := by
  exact prepare2general k ([false]++L)
private theorem prepare2blank (k : Nat) : run0 (table 2) (2*k+6) ⟨0,[],R1 k⟩ = some ⟨0,rep ZZ k++[true],R1 0⟩ := by
  have he : run0 (table 2) (2*k+6) ⟨0,[],R1 k⟩ = run0 (table 2) (2*k+6) ⟨0,[false],R1 k⟩ := by
    rw [show 2*k+6=(2*k+5)+1 by omega]; rfl
  exact he.trans (prepare2general k [])
private theorem finish2 (k : Nat) (L : List Bool) : run0 (table 2) 2 ⟨0,M1++L,R1 k⟩ = some ⟨0,L,R1 (k+1)⟩ := by rfl
private theorem finish2blank (k : Nat) : run0 (table 2) 2 ⟨0,[true],R1 k⟩ = some ⟨0,[],R1 (k+1)⟩ := by rfl

theorem carry0 (k : Nat) : run0 (table 0) (Carry.cost 6 k) ⟨4,[],R0 k⟩ = some ⟨4,[],R0 (k+1)⟩ :=
  Carry.blank (table 0) 4 ZZ M0 M0 R0 4 2 prepare0 finish0 prepare0blank finish0blank k

theorem carry1 (k : Nat) : run0 (table 1) (Carry.cost 4 k) ⟨4,[],R0 k⟩ = some ⟨4,[],R0 (k+1)⟩ :=
  Carry.blank (table 1) 4 ZZ M1 [true] R0 2 2 prepare1 finish1 prepare1blank finish1blank k

theorem carry2 (k : Nat) : run0 (table 2) (Carry.cost 8 k) ⟨0,[],R1 k⟩ = some ⟨0,[],R1 (k+1)⟩ :=
  Carry.blank (table 2) 0 ZZ M1 [true] R1 6 2 prepare2 finish2 prepare2blank finish2blank k

theorem first0 : run0 (table 0) 15 ⟨0,[],[]⟩ = some ⟨4,[],R0 1⟩ := by rfl
theorem first1 : run0 (table 1) 13 ⟨0,[],[]⟩ = some ⟨4,[],R0 1⟩ := by rfl
theorem first2 : run0 (table 2) 32 ⟨0,[],[]⟩ = some ⟨0,[],R1 2⟩ := by rfl

def family (n : Nat) : Z0 := ⟨4,rep M0 (n+1)++ZZ++rep [true] n,[]⟩
private theorem rep_add (X : List Bool) (a b : Nat) : rep X (a+b) = rep X a++rep X b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [show a+1+b=(a+b)+1 by omega,rep,ih,List.append_assoc]
private theorem start34 (v : Nat) (hv : v=3 ∨ v=4) (n : Nat) : run0 (table v) 3 (family n) = some ⟨0,[true]++rep M0 (n+1)++ZZ++rep [true] n,[true]⟩ := by
  rcases hv with rfl|rfl <;> rfl
private theorem aSweep34 (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨0,[true]++M0++L,R⟩ = some ⟨0,[true]++L,Q++R⟩ := by rfl
private theorem aEnd34 (v : Nat) (L R : List Bool) : run0 (table v) 2 ⟨0,[true]++ZZ++L,R⟩ = some ⟨0,[false]++L,Q++R⟩ := by rfl
private theorem turn34 (v : Nat) (hv : v=3 ∨ v=4) (L R : List Bool) : run0 (table v) 8 ⟨0,[false]++L,Q++Q++R⟩ = some ⟨4,[true,true,false,false,true]++L,R⟩ := by
  rcases hv with rfl|rfl <;> cases R with
  | nil => rfl
  | cons a R => cases a <;> rfl
private def rCost (v : Nat) : Nat := if v=3 then 2 else 4
private theorem eRight34 (v : Nat) (hv : v=3 ∨ v=4) (L R : List Bool) : run0 (table v) (rCost v) ⟨4,[true]++L,Q++R⟩ = some ⟨4,[true]++M1++L,R⟩ := by rcases hv with rfl|rfl <;> rfl
private theorem eEnd34 (v : Nat) (hv : v=3 ∨ v=4) (L : List Bool) : run0 (table v) (rCost v) ⟨4,[true]++L,[true]⟩ = some ⟨4,[false,true,false]++L,[]⟩ := by rcases hv with rfl|rfl <;> rfl

theorem grow34 (v n : Nat) (hv : v=3 ∨ v=4) : run0 (table v) (3+2*(n+1)+2+8+rCost v*n+rCost v) (family n) = some (family (n+1)) := by
  have h0 := start34 v hv n
  have h1 := sweepL (table v) 0 [true] [] M0 Q 2 (aSweep34 v) (n+1) (ZZ++rep [true] n) [true]
  simp only [List.nil_append,List.append_assoc] at h0 h1
  have h2 := aEnd34 v (rep [true] n) (rep Q (n+1)++[true])
  have h := join0 (join0 h0 h1) h2
  have hr : Q++(rep Q (n+1)++[true]) = Q++Q++(rep Q n++[true]) := by simp only [rep,List.append_assoc]
  rw [hr] at h
  have h3 := turn34 v hv (rep [true] n) (rep Q n++[true])
  have h4 := sweepR (table v) 4 [true] [] Q M1 (rCost v) (eRight34 v hv) n ([true,false,false,true]++rep [true] n) [true]
  simp only [List.nil_append] at h4
  have h5 := eEnd34 v hv (rep M1 n++([true,false,false,true]++rep [true] n))
  have H := join0 (join0 (join0 h h3) h4) h5
  have hl : [false,true,false]++(rep M1 n++([true,false,false,true]++rep [true] n)) = (family (n+1)).l := by
    have rot : [false]++rep M1 n=rep M0 n++[false] := rotate false [true] n
    calc
      _ = M0++([false]++rep M1 n)++([true,false,false,true]++rep [true] n) := by simp only [List.append_assoc]; rfl
      _ = M0++(rep M0 n++[false])++([true,false,false,true]++rep [true] n) := by rw [rot]
      _ = (M0++rep M0 n)++M0++ZZ++([true]++rep [true] n) := by simp only [List.append_assoc]; rfl
      _ = (family (n+1)).l := by
        unfold family
        change rep M0 (n+1)++M0++ZZ++rep [true] (n+1) = rep M0 (n+1+1)++ZZ++rep [true] (n+1)
        rw [rep_add M0 (n+1) 1]
        rfl
  rw [hl] at H
  exact H

theorem grow3 (n : Nat) : run0 (table 3) (4*n+17) (family n) = some (family (n+1)) := by
  have h := grow34 3 n (Or.inl rfl)
  rw [show 3+2*(n+1)+2+8+rCost 3*n+rCost 3=4*n+17 by simp [rCost] <;> omega] at h
  exact h

theorem grow4 (n : Nat) : run0 (table 4) (6*n+19) (family n) = some (family (n+1)) := by
  have h := grow34 4 n (Or.inr rfl)
  rw [show 3+2*(n+1)+2+8+rCost 4*n+rCost 4=6*n+19 by simp [rCost] <;> omega] at h
  exact h

theorem first3 : run0 (table 3) 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem first4 : run0 (table 4) 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never0 (m : Machine) (hm : compatible (table 0) m) : NeverHalts m :=
  never_of_growth (table 0) (fun i => ⟨4,[],R0 (i+1)⟩) 15
    (fun i => Carry.cost 6 (i+1)) first0 (fun i => Carry.cost_pos 6 (i+1) (by decide))
    (fun i => carry0 (i+1)) m hm
theorem never1 (m : Machine) (hm : compatible (table 1) m) : NeverHalts m :=
  never_of_growth (table 1) (fun i => ⟨4,[],R0 (i+1)⟩) 13
    (fun i => Carry.cost 4 (i+1)) first1 (fun i => Carry.cost_pos 4 (i+1) (by decide))
    (fun i => carry1 (i+1)) m hm
theorem never2 (m : Machine) (hm : compatible (table 2) m) : NeverHalts m :=
  never_of_growth (table 2) (fun i => ⟨0,[],R1 (i+2)⟩) 32
    (fun i => Carry.cost 8 (i+2)) first2 (fun i => Carry.cost_pos 8 (i+2) (by decide))
    (fun i => by simpa only [show i+2+1=(i+1)+2 by omega] using carry2 (i+2)) m hm
theorem never3 (m : Machine) (hm : compatible (table 3) m) : NeverHalts m :=
  never_of_growth (table 3) family 9 (fun i => 4*i+17) first3 (fun i => by omega) grow3 m hm
theorem never4 (m : Machine) (hm : compatible (table 4) m) : NeverHalts m :=
  never_of_growth (table 4) family 9 (fun i => 6*i+19) first4 (fun i => by omega) grow4 m hm
theorem never (v : Nat) (hv : v<5) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  exact never0 m hm
  exact never1 m hm
  exact never2 m hm
  exact never3 m hm
  exact never4 m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0RD
