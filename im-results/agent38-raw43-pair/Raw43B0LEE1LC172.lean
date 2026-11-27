import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE1LC172
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def O : List Bool := [false,true,false,true]
def I : List Bool := [true,true,true,true]
def family (n : Nat) : Z0 := ⟨0,[],rep O (n+1)⟩

theorem forward (n : Nat) (L R : List Bool) :
  run0 table (6*n) ⟨0,false::L,rep O n++R⟩ = some ⟨0,false::(rep I n++L),R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 6 ⟨0,false::L, O++(rep O n++R)⟩ = some ⟨0,false::(I++L),rep O n++R⟩ := by rfl
    have h2 := ih (I++L)
    rw [Nat.mul_succ, Nat.add_comm (6*n) 6]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep I n) I L,rep_snoc I n] using join0 h1 h2

theorem back (n : Nat) (L R : List Bool) :
    run0 table (4*n) ⟨0,rep I n++L,R⟩ = some ⟨0,L,rep O n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 4 ⟨0,I++(rep I n++L),R⟩ = some ⟨0,rep I n++L,O++R⟩ := by rfl
    have h2 := ih (O++R)
    rw [Nat.mul_succ, Nat.add_comm (4*n) 4]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O R,rep_snoc O n] using join0 h1 h2

def cost (n : Nat) : Nat := 10*n+21

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 : run0 table 6 (family n) = some ⟨0,false::I,rep O n⟩ := by rfl
  have h2 := forward n I []
  simp only [List.append_nil] at h2
  have h3 : run0 table 11 ⟨0,false::(rep I n++I),[]⟩ = some ⟨0,rep I n++I,O⟩ := by
    cases n <;> rfl
  have h4 := back (n+1) [] O
  simp only [List.append_nil] at h4
  have h5 : rep I n ++ I = rep I (n+1) := by rw [rep_snoc,rep]
  rw [h5] at h3
  rw [h5] at h2
  have h := join0 (join0 (join0 h1 h2) h3) h4
  have heq : 6+6*n+11+4*(n+1)=cost n := by unfold cost; omega
  rw [heq] at h
  have h6 : rep O (n+1) ++ O = rep O (n+2) := by rw [rep_snoc]; rfl
  rw [h6] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 cost (by rfl) (by intro n; unfold cost; omega) growth m hm

#print axioms never
end BB6.Agent38Raw43B0LEE1LC172
