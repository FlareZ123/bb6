import SweepPumping
namespace BB6.Agent10Raw108RD441
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev P : List Bool := [true,false,true]
abbrev Q : List Bool := [false,true,false]
abbrev X : List Bool := [false,false,true]
abbrev U : List Bool := [false,false,true]
abbrev V : List Bool := [false,false,false,true]

theorem commute (W : List Bool) (k : Nat) (R : List Bool) : rep W k ++ (W++R) = W ++ (rep W k++R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (W++rep W k)++(W++R) = W++((W++rep W k)++R)
    simp only [List.append_assoc,ih]

theorem transfer (L R : List Bool) : run0 table 3 (A (U++L) (Q++R)) = some (A (U++P++L) R) := by rfl

theorem advance (n : Nat) (L R : List Bool) : run0 table (3*n) (A (U++L) (rep Q n++R)) = some (A (U++rep P n++L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (transfer L (rep Q n++R)) (ih (P++L))
    rw [List.append_assoc U (rep P n) (P++L),commute] at h
    simpa only [rep,List.append_assoc,Nat.mul_succ,Nat.add_comm] using h

theorem reset (L : List Bool) : run0 table 20 (A (U++L) V) = some (F (P++L) (false::V)) := by rfl

theorem back_one (L R : List Bool) : run0 table 7 (F (P++L) R) = some (F L (X++R)) := by rfl

theorem back_all (n : Nat) (L R : List Bool) : run0 table (7*n) (F (rep P n++L) R) = some (F L (rep X n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h := join0 (back_one (rep P n++L) R) (ih (X++R))
    rw [commute] at h
    simpa only [rep,List.append_assoc,Nat.mul_succ,Nat.add_comm] using h

theorem rotate (n : Nat) : rep X n ++ false::V = false::(rep Q n++V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change X ++ (rep X n++false::V) = false::(Q++(rep Q n++V))
    rw [ih]
    rfl

theorem finish (R : List Bool) : run0 table 3 (F [] (false::R)) = some (A U R) := by rfl

def family (n : Nat) := A U (rep Q n++V)
def cost (n : Nat) := 3*n+20+7*(n+1)+3

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := by simp [cost]
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h₁ := advance n [] V
  simp only [List.append_nil] at h₁
  have h₂ := reset (rep P n)
  have h₃ := back_all (n+1) [] (false::V)
  simp only [List.append_nil,rotate] at h₃
  have h₄ := finish (rep Q (n+1)++V)
  exact join0 (join0 (join0 h₁ h₂) h₃) h₄

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 cost entry positive growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108RD441
