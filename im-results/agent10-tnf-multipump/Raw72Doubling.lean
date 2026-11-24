import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Recursive.R72M170
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1LE_1RC1RC_0RD1RF_1LD1RE_1LA0LB_---1RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
abbrev alt (n : Nat) := rep [true,false] n
def A (m : Nat) : Z0 := ⟨0,[],O m⟩
def D (k r : Nat) : Z0 := ⟨3,[false,false]++alt k++O r,[]⟩
theorem rep_ones (a n : Nat) : rep (O a) n = O (a*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,List.replicate_append_replicate]
    congr 1 <;> simp [Nat.mul_succ,Nat.add_comm]

theorem leftLocal (L R : List Bool) : run0 table 2 ⟨0,[true,false]++L,R⟩ = some ⟨0,L,[true,true]++R⟩ := by rfl

theorem enterA (k r : Nat) : run0 table (8+2*(k+1)) (D k (r+1)) = some ⟨0,O (r+1),O (2*k+3)⟩ := by
  have h1 : run0 table 8 (D k (r+1)) = some ⟨0,alt (k+1)++O (r+1),[true]⟩ := by
    cases k <;> rfl
  have h2 := sweepL table 0 [] [] [true,false] [true,true] 2 leftLocal (k+1) (O (r+1)) [true]
  change run0 table (2*(k+1)) ⟨0,alt (k+1)++O (r+1),[true]⟩ = some ⟨0,O (r+1),rep [true,true] (k+1)++[true]⟩ at h2
  have he : rep [true,true] (k+1)++[true] = O (2*k+3) := by
    change rep (O 2) (k+1)++O 1 = O (2*k+3)
    rw [rep_ones,List.replicate_append_replicate]
    congr 1 <;> simp [Nat.mul_succ,Nat.add_comm]
  rw [he] at h2
  exact join0 h1 h2

theorem rightLocal (L R : List Bool) : run0 table 4 ⟨3,[true,false]++L,[true,true]++R⟩ = some ⟨3,[true,false]++[true,false]++L,R⟩ := by rfl

theorem sweepExit (k : Nat) (L : List Bool) :
    run0 table (4*(k+1)+4) ⟨3,[true,false]++L,O (2*k+3)⟩ = some ⟨3,[false,false]++alt (k+2)++L,[]⟩ := by
  have h := sweepR table 3 [true,false] [] [true,true] [true,false] 4 rightLocal (k+1) L [true]
  change run0 table (4*(k+1)) ⟨3,[true,false]++L,rep [true,true] (k+1)++[true]⟩ = some ⟨3,[true,false]++alt (k+1)++L,[true]⟩ at h
  have he : rep [true,true] (k+1)++[true] = O (2*k+3) := by
    change rep (O 2) (k+1)++O 1 = O (2*k+3)
    rw [rep_ones,List.replicate_append_replicate]
    congr 1 <;> simp [Nat.mul_succ,Nat.add_comm]
  rw [he] at h
  have h2 : run0 table 4 ⟨3,[true,false]++alt (k+1)++L,[true]⟩ = some ⟨3,[false,false]++alt (k+2)++L,[]⟩ := by rfl
  exact join0 h h2

def loopCost (k : Nat) := 8+2*(k+1)+4+(4*(k+1)+4)
theorem Dloop (k r : Nat) : run0 table (loopCost k) (D k (r+3)) = some (D (k+2) (r+1)) := by
  have h1 := enterA k (r+2)
  have h2 : run0 table 4 ⟨0,O (r+3),O (2*k+3)⟩ = some ⟨3,[true,false]++O (r+1),O (2*k+3)⟩ := by rfl
  have h3 := sweepExit k (O (r+1))
  exact join0 (join0 h1 h2) h3

theorem Dtwo (k : Nat) : run0 table (loopCost k) (D k 2) = some (D (k+2) 1) := by
  have h1 := enterA k 1
  have h2 : run0 table 4 ⟨0,O 2,O (2*k+3)⟩ = some ⟨3,[true,false]++O 1,O (2*k+3)⟩ := by rfl
  have h3 := sweepExit k (O 1)
  exact join0 (join0 h1 h2) h3

theorem Done (k : Nat) : run0 table (8+2*(k+1)+2) (D k 1) = some (A (2*k+5)) := by
  have h1 := enterA k 0
  have h2 : run0 table 2 ⟨0,O 1,O (2*k+3)⟩ = some (A (2*k+5)) := by rfl
  exact join0 h1 h2

def dCost : Nat → Nat → Nat
  | k,0 => 8+2*(k+1)+2
  | k,j+1 => loopCost k + dCost (k+2) j

def eCost : Nat → Nat → Nat
  | k,0 => loopCost k + dCost (k+2) 0
  | k,j+1 => loopCost k + eCost (k+2) j

theorem Dodd (k j : Nat) : run0 table (dCost k j) (D k (2*j+1)) = some (A (2*k+4*j+5)) := by
  induction j generalizing k with
  | zero => exact Done k
  | succ j ih =>
    have h1 := Dloop k (2*j)
    have h2 := ih (k+2)
    have h := join0 h1 h2
    rw [show 2*(k+2)+4*j+5 = 2*k+4*(j+1)+5 by omega] at h
    exact h

theorem Deven (k j : Nat) : run0 table (eCost k j) (D k (2*j+2)) = some (A (2*k+4*j+9)) := by
  induction j generalizing k with
  | zero =>
    have h := join0 (Dtwo k) (Done (k+2))
    rw [show 2*(k+2)+5 = 2*k+4*0+9 by omega] at h
    exact h
  | succ j ih =>
    have h1 := Dloop k (2*j+1)
    have h2 := ih (k+2)
    have h := join0 h1 h2
    rw [show 2*(k+2)+4*j+9 = 2*k+4*(j+1)+9 by omega] at h
    exact h

theorem Blocal (L R : List Bool) : run0 table 3 ⟨1,[true]++L,[true,true,true]++R⟩ = some ⟨1,[true]++[true,true,true]++L,R⟩ := by rfl

theorem Bphase (n r : Nat) : run0 table (3*n) ⟨1,O 2,O (3*n+r)⟩ = some ⟨1,O (3*n+2),O r⟩ := by
  have h := sweepR table 1 [true] [] [true,true,true] [true,true,true] 3 Blocal n [true] (O r)
  change run0 table (3*n) ⟨1,O 2,rep (O 3) n++O r⟩ = some ⟨1,O 1++rep (O 3) n++O 1,O r⟩ at h
  simp only [rep_ones,List.replicate_append_replicate] at h
  rw [show 1+3*n+1=3*n+2 by omega] at h
  exact h

theorem AtoD1 (n : Nat) : run0 table (1+3*n+2) (A (3*n+1)) = some (D 0 (3*n+2)) := by
  have h1 : run0 table 1 (A (3*n+1)) = some ⟨1,O 2,O (3*n)⟩ := by rfl
  have h2 := Bphase n 0
  have h3 : run0 table 2 ⟨1,O (3*n+2),[]⟩ = some (D 0 (3*n+2)) := by rfl
  exact join0 (join0 h1 h2) h3

theorem AtoD0 (n : Nat) : run0 table (1+3*n+5) (A (3*n+3)) = some (D 0 (3*n+5)) := by
  have h1 : run0 table 1 (A (3*n+3)) = some ⟨1,O 2,O (3*n+2)⟩ := by rfl
  have h2 := Bphase n 2
  have h3 : run0 table 5 ⟨1,O (3*n+2),O 2⟩ = some (D 0 (3*n+5)) := by rfl
  exact join0 (join0 h1 h2) h3

theorem section_return (m : Nat) (hodd : m % 2 = 1) (h3 : m % 3 ≠ 2) : ∃ t, 0<t ∧ run0 table t (A m) = some (A (2*m+7)) := by
  by_cases h : m % 3 = 1
  · have h1 := AtoD1 (m/3)
    rw [show 3*(m/3)+1=m by omega,show 3*(m/3)+2=2*(m/2)+2 by omega] at h1
    have h2 := Deven 0 (m/2)
    rw [show 2*0+4*(m/2)+9=2*m+7 by omega] at h2
    exact ⟨_,by omega,join0 h1 h2⟩
  · have h1 := AtoD0 (m/3-1)
    rw [show 3*(m/3-1)+3=m by omega,show 3*(m/3-1)+5=2*(m/2+1)+1 by omega] at h1
    have h2 := Dodd 0 (m/2+1)
    rw [show 2*0+4*(m/2+1)+5=2*m+7 by omega] at h2
    exact ⟨_,by omega,join0 h1 h2⟩

def mass : Nat → Nat
  | 0 => 9
  | n+1 => 2*mass n+7

theorem mass_ok (n : Nat) : mass n % 2 = 1 ∧ mass n % 3 ≠ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [mass]
    omega

def family (n : Nat) := A (mass n)
theorem entry : run0 table 41 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem family_step (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) :=
  section_return (mass n) (mass_ok n).1 (mass_ok n).2
noncomputable def cost (n : Nat) : Nat := (family_step n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (family_step n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (family_step n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 41 cost entry cost_pos growth m hm
#print axioms section_return
#print axioms never
end BB6.Agent10Recursive.R72M170
