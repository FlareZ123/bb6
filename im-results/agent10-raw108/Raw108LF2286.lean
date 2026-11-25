import SweepPumping
namespace BB6.Agent10Raw108LF2286
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev P : List Bool := [true,true]
abbrev Q : List Bool := [true]
abbrev Z : List Bool := [false,false]

theorem repAdd (w : List Bool) (a b : Nat) :
    rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep]
    simp only [List.append_assoc]
theorem doubleRep (n : Nat) : rep P n = rep Q (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,repAdd Q (2*n) 2,← ih]
    rw [rep,← rep_snoc P n]
    rfl

theorem first (R : List Bool) :
    run0 table 7 (A [] (Z++true::(P++R))) = some (A P (Z++P++R)) := by rfl
theorem advance (L R : List Bool) :
    run0 table 14 (A (P++L) (Z++P++P++R)) =
      some (A (P++P++L) (Z++P++R)) := by rfl
theorem shift (L : List Bool) :
    run0 table 20 (A (P++L) (Z++P)) =
      some (D ([true,true,true,true,true,true,true,true]++L) P) := by rfl
theorem drain (L R : List Bool) :
    run0 table 5 (D (Q++Q++L) (Q++R)) =
      some (D (Q++L) (Q++Q++R)) := by rfl
theorem last (R : List Bool) :
    run0 table 4 (D Q (Q++R)) = some (A [] (Z++Q++R)) := by rfl

def family (n : Nat) := A [] (Z++rep Q (6*n+3))

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) :
    run0 table (66+72*n) (family n) = some (family (n+1)) := by
  have h1 := first (rep P (3*n))
  have h2 := sweepR table 0 P (Z++P) P P 14 (by
    intro L R
    simpa only [List.append_assoc] using advance L R) (3*n) [] []
  have h2' : run0 table (14*(3*n)) (A P (Z++P++rep P (3*n))) =
      some (A (P++rep P (3*n)) (Z++P)) := by
    simpa only [List.append_assoc,List.nil_append,List.append_nil,A] using h2
  have h3 := shift (rep P (3*n))
  have H := join0 (join0 h1 h2') h3
  have hL : [true,true,true,true,true,true,true,true]++rep P (3*n) =
      Q++rep Q (6*n+7) := by
    rw [doubleRep,show 2*(3*n)=6*n by omega]
    change rep Q 8 ++ rep Q (6*n) = rep Q 1++rep Q (6*n+7)
    rw [← repAdd Q 8 (6*n),← repAdd Q 1 (6*n+7)]
    congr 1 <;> omega
  rw [hL] at H
  have h4 := sweepL table 3 Q Q Q Q 5 drain (6*n+7) [] Q
  have h4' : run0 table (5*(6*n+7)) (D (Q++rep Q (6*n+7)) P) =
      some (D Q (Q++rep Q (6*n+7)++Q)) := by
    simpa only [List.append_assoc,List.nil_append,List.append_nil,D,P,Q,List.cons_append] using h4
  have h5 := last (rep Q (6*n+7)++Q)
  have G := join0 (join0 H h4') h5
  rw [show 7+14*(3*n)+20+5*(6*n+7)+4 = 66+72*n by omega] at G
  have hR : true::(P++rep P (3*n)) = rep Q (6*n+3) := by
    rw [← rep_snoc P (3*n)]
    change Q++(rep P (3*n)++rep P 1) = _
    rw [← repAdd P (3*n) 1, doubleRep]
    change rep Q 1++rep Q (2*(3*n+1)) = rep Q (6*n+3)
    rw [←repAdd]
    congr 1 <;> omega
  rw [hR] at G
  have hR' : Q++(rep Q (6*n+7)++Q) = rep Q (6*(n+1)+3) := by
    change rep Q 1++(rep Q (6*n+7)++rep Q 1) = _
    rw [←repAdd,←repAdd]
    congr 1 <;> omega
  unfold family
  simpa only [List.append_assoc,hR'] using G

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 66+72*n) entry (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LF2286
