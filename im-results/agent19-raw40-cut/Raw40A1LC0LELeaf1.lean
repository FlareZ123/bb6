import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LC0LE.Leaf1
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

abbrev U : List Bool := [true]
abbrev W : List Bool := [true,true,true,true]
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := P++P
abbrev F : List Bool := [true,false,true,true,true]
abbrev G : List Bool := [true,true]

def family (n : Nat) : Z0 := ⟨0,[],[false,false]++rep W (n+2)++U⟩
def cost (n : Nat) := 150+56*n

theorem entry : run0 table 145 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (R : List Bool) : run0 table 15 ⟨0,[],[false,false]++W++R⟩ =
    some ⟨0,F++[false],[false]++R⟩ := by rfl

theorem forward (L R : List Bool) : run0 table 24 ⟨0,F++L,[false]++W++R⟩ =
    some ⟨0,F++Q++L,[false]++R⟩ := by rfl

theorem turn (L : List Bool) : run0 table 25 ⟨0,F++L,[false,true]⟩ =
    some ⟨0,G++Q++L,[true,true,true]⟩ := by rfl

theorem back (L R : List Bool) : run0 table 16 ⟨0,G++P++L,[true,true,true]++R⟩ =
    some ⟨0,G++L,[true,true,true]++G++R⟩ := by rfl

theorem finish (R : List Bool) : run0 table 22 ⟨0,G++[false],[true,true,true]++R⟩ =
    some ⟨0,[],[false,false]++[true,true,true,true,true]++R⟩ := by rfl

theorem repAdd (p : List Bool) (n m : Nat) : rep p (n+m)=rep p n++rep p m := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega,rep,ih]
    simp only [rep,List.append_assoc]

theorem doubleRep (p : List Bool) (n : Nat) : rep (p++p) n=rep p (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,repAdd]
    simp [rep]

theorem epoch (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := start (rep W (n+1)++U)
  have h2 := sweepR table 0 F [false] W Q 24 forward (n+1) [false] U
  have h3 := turn (rep Q (n+1)++[false])
  have h4 := sweepL table 0 G [true,true,true] P G 16 back (2*n+4) [false] []
  have h5 := finish (rep G (2*n+4))
  simp only [List.append_assoc,List.append_nil] at h1 h2 h3 h4 h5
  have H := join0 (join0 h1 h2) h3
  have he : Q++rep Q (n+1)=rep P (2*n+4) := by
    change rep Q 1++rep Q (n+1)=_
    rw [←repAdd,show 1+(n+1)=n+2 by omega,doubleRep P]
    rw [show 2*(n+2)=2*n+4 by omega]
  have he' : G++(Q++(rep Q (n+1)++[false]))=G++(rep P (2*n+4)++[false]) := by
    rw [←List.append_assoc Q,he]
  change run0 table (15+24*(n+1)+25) ⟨0,[],[false,false]++(W++(rep W (n+1)++U))⟩ = some ⟨0,G++(Q++(rep Q (n+1)++[false])),[true,true,true]⟩ at H
  rw [he'] at H
  have H := join0 (join0 H h4) h5
  have hr : [true,true,true,true,true]++rep G (2*n+4)=rep W (n+3)++U := by
    change rep U 5++rep G (2*n+4)=rep W (n+3)++rep U 1
    have hG : ∀ k, rep G k=rep U (2*k) := doubleRep U
    have hW : ∀ k, rep W k=rep G (2*k) := doubleRep G
    rw [hW,hG,hG,←repAdd,←repAdd]
    congr 1
    omega
  rw [hr] at H
  simpa only [cost,family,rep,List.append_assoc,show n+1+2=n+3 by omega,
    show 15+24*(n+1)+25+16*(2*n+4)+22=150+56*n by omega] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 145 cost entry (by intro n; unfold cost; omega) epoch m hm
#print axioms never
end BB6.Agent19Raw40.A1LC0LE.Leaf1
