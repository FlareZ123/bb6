import SweepPumping
namespace BB6.Agent10Raw108RC100
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B : List Bool := [true,false,true,true]
abbrev P : List Bool := B ++ [false]
abbrev Q : List Bool := false::B

theorem rotate (k : Nat) : B ++ rep Q k = rep P k ++ B := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change B ++ (Q ++ rep Q k) = P ++ (rep P k ++ B)
    change P ++ (B ++ rep Q k) = P ++ (rep P k ++ B)
    rw [ih]

theorem commute (W : List Bool) (k : Nat) (R : List Bool) : rep W k ++ (W++R) = W ++ (rep W k++R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (W++rep W k)++(W++R) = W++((W++rep W k)++R)
    simp only [List.append_assoc,ih]

theorem out_one (L R : List Bool) : run0 table 7 (A (P++L) R) = some (A L (P++R)) := by rfl
theorem out_all (k : Nat) (L R : List Bool) : run0 table (7*k) (A (rep P k++L) R) = some (A L (rep P k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (out_one (rep P k++L) R) (ih (P++R))
    rw [commute] at h
    simpa only [rep,List.append_assoc,Nat.mul_succ,Nat.add_comm] using h

theorem out_end (R : List Bool) : run0 table 7 (A B R) = some (A [] (P++R)) := by rfl

theorem back_start (R : List Bool) : run0 table 7 (A [] (P++R)) = some (A (false::Q) R) := by rfl

theorem back_one (L R : List Bool) : run0 table 7 (A (false::L) (P++R)) = some (A (false::Q++L) R) := by rfl

theorem back_all (k : Nat) (L : List Bool) : run0 table (7*k) (A (false::L) (rep P k)) = some (A (false::(rep Q k++L)) []) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (back_one L (rep P k)) (ih (Q++L))
    rw [commute] at h
    simpa only [rep,List.append_assoc,List.cons_append,Nat.mul_succ,Nat.add_comm] using h

theorem expand (L : List Bool) : run0 table 9 (A (false::L) []) = some (A (B++L) []) := by rfl

def family (k : Nat) := A (B++rep Q k) []
def cost (k : Nat) := 7*k+7+7+7*k+9

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (k : Nat) : 0 < cost k := by simp [cost]
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h₁ := out_all k B []
  rw [List.append_nil] at h₁
  have h₂ := out_end (rep P k)
  have h₃ := back_start (rep P k)
  have h₄ := back_all k Q
  have h₅ := expand (rep Q k++Q)
  have h := join0 (join0 (join0 (join0 h₁ h₂) h₃) h₄) h₅
  unfold family cost
  rw [rotate]
  have e := commute Q k []
  simp only [List.append_nil] at e
  rw [e] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry positive growth m hm

#print axioms growth
#print axioms never
end BB6.Agent10Raw108RC100
