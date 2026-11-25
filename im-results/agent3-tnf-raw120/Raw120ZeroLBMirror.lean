import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120ZeroLBMirror
open BB6Coverage BB6Coverage.Agent31Pump

/-- raw120 0LB leaf 2098. The missing C1 transition is never queried. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev S (L : List Bool) := false::true::L

def T : Nat → Nat | 0 => 13 | n+1 => 2*T n+11

theorem core (n : Nat) (L R : List Bool) (b : Bool) :
    run0 table (T n) ⟨4,O (3*n+2)++S L,b::R⟩ =
      some ⟨1,b::(O (3*n+2)++S L),R⟩ := by
  induction n generalizing R b with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)+2=3*n+2+1+1+1 by omega]
    simp only [List.replicate_succ,List.cons_append]
    have h1 : run0 table 3 ⟨4,true::true::true::(O (3*n+2)++S L),b::R⟩ =
        some ⟨4,O (3*n+2)++S L,true::true::true::b::R⟩ := by rfl
    have h2 := ih (true::true::b::R) true
    have h3 : run0 table 5 ⟨1,true::(O (3*n+2)++S L),true::true::b::R⟩ =
        some ⟨4,O (3*n+2)++S L,true::true::false::b::R⟩ := by rfl
    have h4 := ih (true::false::b::R) true
    have h5 : run0 table 3 ⟨1,true::(O (3*n+2)++S L),true::false::b::R⟩ =
        some ⟨1,b::true::true::true::(O (3*n+2)++S L),R⟩ := by rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 3+T n+5+T n+3=T (n+1) by simp [T]; omega] at h
    exact h

def family (n : Nat) : Z0 := ⟨1,false::(O (3*n+5)++S []),[]⟩

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem step (n : Nat) :
    run0 table (2*T (n+1)+15) (family n) = some (family (n+1)) := by
  have h1 : run0 table 7 (family n) =
      some ⟨4,O (3*n+5)++S [],[true,true,true]⟩ := by rfl
  have h2 := core (n+1) [] [true,true] true
  rw [show 3*(n+1)+2=3*n+5 by omega] at h2
  have h3 : run0 table 5 ⟨1,true::(O (3*n+5)++S []),[true,true]⟩ =
      some ⟨4,O (3*n+5)++S [],[true,true,false]⟩ := by rfl
  have h4 := core (n+1) [] [true,false] true
  rw [show 3*(n+1)+2=3*n+5 by omega] at h4
  have h5 : run0 table 3 ⟨1,true::(O (3*n+5)++S []),[true,false]⟩ =
      some (family (n+1)) := by
    unfold family
    rw [show 3*(n+1)+5=3*n+5+1+1+1 by omega]
    rfl
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 7+T (n+1)+5+T (n+1)+3=2*T (n+1)+15 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 29 (fun n => 2*T (n+1)+15) entry (by intro n; omega) step m hm
#print axioms never
end BB6.Agent3Raw120ZeroLBMirror
