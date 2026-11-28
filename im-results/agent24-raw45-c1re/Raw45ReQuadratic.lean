import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45.ReQuadratic
open BB6Coverage BB6Coverage.Agent31Pump

/-- The hard C1=1RE, E0=1LA, E1=1RF, F1=0RB residual. F0 is unassigned. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

private def I : List Bool := [true,true]
private def P : List Bool := [true,false]
private def Q : List Bool := I++I
private def W : List Bool := P++P

def d (n : Nat) : Z0 := ⟨3,[false,false]++rep I (n+1),[]⟩
def e (a b : Nat) : Z0 := ⟨4,Q,rep W a++I++rep P b++[true]⟩

private theorem rep_add' (s : List Bool) (a b : Nat) : rep s a ++ rep s b = rep s (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [rep,List.append_assoc,ih,show a+1+b=a+b+1 by omega]

private theorem rep_double (s : List Bool) (n : Nat) : rep (s++s) n = rep s (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2*n+2 by omega,show 2*n+2=2+2*n by omega,←rep_add']
    simp [rep,List.append_assoc]

private theorem ones_commute (n : Nat) : [true]++rep I n = rep I n++[true] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc]; rw [←ih]; rfl

private theorem bPair (L R : List Bool) :
    run0 table 2 ⟨1,I++L,R⟩ = some ⟨1,L,P++R⟩ := by rfl

private theorem bSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨1,rep I n++L,R⟩ = some ⟨1,L,rep P n++R⟩ := by
  simpa only [List.nil_append] using sweepL table 1 [] [] I P 2 bPair n L R

private theorem ePacket (L R : List Bool) :
    run0 table 10 ⟨4,Q++L,W++R⟩ = some ⟨4,Q++Q++L,R⟩ := by rfl

private theorem eSweep (a : Nat) (R : List Bool) :
    run0 table (10*a) ⟨4,Q,rep W a++R⟩ = some ⟨4,rep Q (a+1),R⟩ := by
  simpa only [List.append_nil,List.nil_append,rep] using sweepR table 4 Q [] W Q 10 ePacket a [] R

private theorem dStart (n : Nat) :
    run0 table 3 (d n) = some ⟨1,rep I (n+1)++[true],[true]⟩ := by
  rw [←ones_commute]
  rfl

private theorem bEnd (n : Nat) :
    run0 table 4 ⟨1,[true],rep P (n+1)++[true]⟩ = some ⟨4,[false,true,true,true],rep P n++[true]⟩ := by rfl

private theorem eStart (R : List Bool) :
    run0 table 12 ⟨4,[false,true,true,true],R⟩ = some ⟨4,Q,I++R⟩ := by rfl

private theorem enter (n : Nat) : run0 table (2*n+21) (d n) = some (e 0 n) := by
  have H := join0 (join0 (join0 (dStart n) (bSweep (n+1) [true] [true])) (bEnd n)) (eStart (rep P n++[true]))
  simpa only [e,rep,List.nil_append,List.append_assoc,show 3+2*(n+1)+4+12=2*n+21 by omega] using H

private theorem resetStart (k : Nat) (R : List Bool) :
    run0 table 2 ⟨4,[false,true]++rep I (k+1),R⟩ = some ⟨1,rep I (k+1),I++R⟩ := by rfl

private theorem resetEnd (k : Nat) (R : List Bool) :
    run0 table 8 ⟨1,[],rep P (k+1)++(I++R)⟩ = some ⟨4,Q,rep P k++(I++R)⟩ := by rfl

private theorem reset (k : Nat) (R : List Bool) :
    run0 table (2*k+12) ⟨4,[false,true]++rep I (k+1),R⟩ = some ⟨4,Q,rep P k++I++R⟩ := by
  have hs : run0 table (2*(k+1)) ⟨1,rep I (k+1),I++R⟩ = some ⟨1,[],rep P (k+1)++(I++R)⟩ := by
    simpa only [List.append_nil] using bSweep (k+1) [] (I++R)
  have H := join0 (join0 (resetStart k R) hs) (resetEnd k R)
  simpa only [List.append_nil,List.append_assoc,show 2+2*(k+1)+8=2*k+12 by omega] using H

private theorem marker (L R : List Bool) :
    run0 table 6 ⟨4,true::L,[true,true,true,false]++R⟩ = some ⟨4,[false,true,true,true,true]++L,R⟩ := by rfl

private theorem markerTail (L : List Bool) :
    run0 table 6 ⟨4,true::L,[true,true,true]⟩ = some ⟨4,[false,true,true,true,true]++L,[]⟩ := by rfl

private theorem markerWide (a : Nat) (R : List Bool) :
    run0 table 6 ⟨4,rep Q (a+1),[true,true,true,false]++R⟩ =
      some ⟨4,[false,true]++rep I (2*a+3),R⟩ := by
  have H := marker ([true,true,true]++rep Q a) R
  rw [show rep I (2*a+3)=rep I 3++rep I (2*a) by rw [rep_add']; congr 1; omega, ←rep_double I a]
  exact H

private theorem markerTailWide (a : Nat) :
    run0 table 6 ⟨4,rep Q (a+1),[true,true,true]⟩ =
      some ⟨4,[false,true]++rep I (2*a+3),[]⟩ := by
  have H := markerTail ([true,true,true]++rep Q a)
  rw [show rep I (2*a+3)=rep I 3++rep I (2*a) by rw [rep_add']; congr 1; omega, ←rep_double I a]
  exact H

private theorem middle (a b : Nat) :
    run0 table (14*a+22) (e a (b+1)) = some (e (a+1) b) := by
  have H1 := eSweep a (I++rep P (b+1)++[true])
  have H2 := markerWide a (rep P b++[true])
  have H3 := reset (2*a+2) (rep P b++[true])
  have H12 : run0 table (10*a+6) (e a (b+1)) =
      some ⟨4,[false,true]++rep I (2*a+3),rep P b++[true]⟩ := by
    apply join0 ?_ H2
    simpa only [e,rep,I,P,List.append_assoc,List.cons_append,List.nil_append] using H1
  have H := join0 H12 H3
  simpa only [e,W,rep_double,List.append_assoc,show 10*a+6+(2*(2*a+2)+12)=14*a+22 by omega,show 2*(a+1)=2*a+2 by omega] using H

def midCost (a : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => 14*a+22+midCost (a+1) b

private theorem mid (a b : Nat) :
    run0 table (midCost a b) (e a b) = some (e (a+b) 0) := by
  induction b generalizing a with
  | zero => simp [midCost,run0]
  | succ b ih =>
    simpa only [midCost,show a+1+b=a+(b+1) by omega] using join0 (middle a b) (ih (a+1))

theorem midCost_exact (a b : Nat) : midCost a b = 7*b*b+(14*a+15)*b := by
  induction b generalizing a with
  | zero => simp [midCost]
  | succ b ih =>
    rw [midCost,ih]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
    omega

private theorem last (L : List Bool) :
    run0 table 6 ⟨4,true::L,I⟩ = some ⟨3,[false,false,true,true,true]++L,[]⟩ := by rfl

private theorem lastWide (a : Nat) :
    run0 table 6 ⟨4,rep Q (a+2),I⟩ = some (d (2*a+4)) := by
  have H := last ([true,true,true]++Q++rep Q a)
  rw [d,show rep I (2*a+4+1)=rep I 5++rep I (2*a) by rw [rep_add']; congr 1; omega,←rep_double I a]
  exact H

private theorem finish (n : Nat) :
    run0 table (24*n+38) (e n 0) = some (d (2*n+4)) := by
  have H1 := eSweep n [true,true,true]
  have H2 := markerTailWide n
  have H3 := reset (2*n+2) []
  have H4 := eSweep (n+1) I
  have H5 := lastWide n
  have H12 : run0 table (10*n+6) (e n 0) = some ⟨4,[false,true]++rep I (2*n+3),[]⟩ := by
    apply join0 ?_ H2
    simpa only [e,rep,I,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H1
  have H123 := join0 H12 H3
  have H1234 : run0 table (10*n+6+(2*(2*n+2)+12)+10*(n+1)) (e n 0) =
      some ⟨4,rep Q (n+2),I⟩ := by
    apply join0 ?_ H4
    simpa only [List.append_nil,W,rep_double,show 2*(n+1)=2*n+2 by omega] using H123
  simpa only [show 10*n+6+(2*(2*n+2)+12)+10*(n+1)+6=24*n+38 by omega] using join0 H1234 H5

/-- The whole D-return, including the nested marker transfer, is exact. -/
theorem growth (n : Nat) :
    run0 table (7*n*n+41*n+59) (d n) = some (d (2*n+4)) := by
  have hmid : run0 table (midCost 0 n) (e 0 n) = some (e n 0) := by simpa only [Nat.zero_add] using mid 0 n
  have H := join0 (join0 (enter n) hmid) (finish n)
  rw [midCost_exact] at H
  simpa only [Nat.zero_add, Nat.mul_zero, Nat.zero_mul, show (2*n+21)+(7*n*n+(14*0+15)*n)+(24*n+38)=7*n*n+41*n+59 by omega] using H

def index : Nat → Nat
  | 0 => 0
  | k+1 => 2*index k+4

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun k => d (index k)) 3 (fun k => 7*(index k)*(index k)+41*(index k)+59) _ _ _ m hm
  · rfl
  · intro k; omega
  · intro k; exact growth (index k)

#print axioms growth
#print axioms never
end BB6.Agent24Raw45.ReQuadratic
