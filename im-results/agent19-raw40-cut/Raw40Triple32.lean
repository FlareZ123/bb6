import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Triple32
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RC_1RC0RE_0RD1RE_1LD1LA_0RF0LB_---0RC
-- F0 is never read.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def U (n : Nat) := rep [true] n
def Z (n : Nat) := rep [false] n
private theorem repAdd (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep,List.append_assoc]
private theorem u2 (k : Nat) : rep [true,true] k = U (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 2*(k+1)=2+2*k by omega]; change _ = rep [true] (2+2*k); rw [repAdd]; rfl
private theorem u3 (k : Nat) : rep [true,true,true] k = U (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 3*(k+1)=3+3*k by omega]; change _ = rep [true] (3+3*k); rw [repAdd]; rfl
private theorem z3 (k : Nat) : rep [false,false,false] k = Z (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 3*(k+1)=3+3*k by omega]; change _ = rep [false] (3+3*k); rw [repAdd]; rfl

theorem bmove (L R : List Bool) : run0 table 6 ⟨1,[true,true]++L,[true,true]++R⟩ =
    some ⟨1,[true,true]++[true,true]++L,R⟩ := by rfl
theorem bturn (L : List Bool) : run0 table 8 ⟨1,[true,true]++L,[true]⟩ =
    some ⟨2,[true,true]++L,[true,true]⟩ := by rfl

theorem prep (j : Nat) : run0 table (6*j+8) ⟨1,[true,true],U (2*j+1)⟩ =
    some ⟨2,U (2*j+2),U 2⟩ := by
  have h1 := sweepR table 1 [true,true] [] [true,true] [true,true] 6 bmove j [] [true]
  simp only [List.nil_append,List.append_nil,u2] at h1
  have h2 := bturn (U (2*j))
  have H := join0 h1 h2
  simpa only [U,repAdd,show rep [true] 1=[true] by rfl,show rep [true] 2=[true,true] by rfl,show 2*j+2=2+2*j by omega] using H

theorem cmove (L R : List Bool) : run0 table 5 ⟨2,[true]++L,[true,true,true]++R⟩ =
    some ⟨2,[true]++[false,false,false]++L,R⟩ := by rfl
theorem cturn (L : List Bool) : run0 table 6 ⟨2,[true]++L,[true,true]⟩ =
    some ⟨3,[false,false,false,false,false]++L,[]⟩ := by rfl
theorem dmove (L R : List Bool) : run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem convert (k : Nat) (L : List Bool) : run0 table (8*k+11) ⟨2,true::L,U (3*k+2)⟩ =
    some ⟨3,L,U (3*k+5)⟩ := by
  have h1 := sweepR table 2 [true] [] [true,true,true] [false,false,false] 5 cmove k L [true,true]
  simp only [List.nil_append,u3,z3,List.append_assoc] at h1
  have h2 := cturn (Z (3*k)++L)
  have h3 := sweepL table 3 [] [] [false] [true] 1 dmove (3*k+5) L []
  have h2' : run0 table 6 ⟨2,true::(Z (3*k)++L),[true,true]⟩ =
      some ⟨3,Z (3*k+5)++L,[]⟩ := by
    rw [show 3*k+5=5+3*k by omega]; change _ = some (⟨3,rep [false] (5+3*k)++L,[]⟩ : Z0); rw [repAdd]
    simpa only [Z,show rep [false] 5=[false,false,false,false,false] by rfl,List.append_assoc,List.singleton_append] using h2
  simp only [List.nil_append,List.append_nil] at h3
  have H := join0 (join0 h1 h2') h3
  simpa only [U,repAdd,show rep [true] 2=[true,true] by rfl,show 5*k+6+1*(3*k+5)=8*k+11 by omega,List.singleton_append] using H

theorem epoch (k b : Nat) : run0 table (8*k+13) ⟨2,U (b+3),U (3*k+2)⟩ =
    some ⟨2,U (b+2),U (3*(k+1)+2)⟩ := by
  have h1 := convert k (U (b+2))
  have h2 : run0 table 2 ⟨3,U (b+2),U (3*k+5)⟩ = some ⟨2,U (b+2),U (3*k+5)⟩ := by
    rw [show b+2=2+b by omega,U,repAdd]; rfl
  have H := join0 h1 h2
  simpa only [show b+3=1+(b+2) by omega,U,repAdd,show rep [true] 1=[true] by rfl,List.singleton_append,show 3*(k+1)+2=3*k+5 by omega,show 8*k+11+2=8*k+13 by omega] using H

theorem finish (k : Nat) : run0 table (8*k+13) ⟨2,U 2,U (3*k+2)⟩ =
    some ⟨1,[true,true],U (3*(k+1)+2)⟩ := by
  have h1 := convert k [true]
  have h2 : run0 table 2 ⟨3,[true],U (3*k+5)⟩ = some ⟨1,[true,true],U (3*k+5)⟩ := by rfl
  simpa only [show U 2=[true,true] by rfl,show 3*(k+1)+2=3*k+5 by omega,show 8*k+11+2=8*k+13 by omega] using join0 h1 h2

def cost (k : Nat) : Nat → Nat
  | 0 => 8*k+13
  | b+1 => 8*k+13+cost (k+1) b

theorem collapse (k b : Nat) : run0 table (cost k b) ⟨2,U (b+2),U (3*k+2)⟩ =
    some ⟨1,[true,true],U (3*(k+b+1)+2)⟩ := by
  induction b generalizing k with
  | zero => simpa [cost] using finish k
  | succ b ih =>
    have H := join0 (epoch k b) (ih (k+1))
    simpa only [cost,show b+1+2=b+3 by omega,show k+1+b+1=k+(b+1)+1 by omega] using H

def family (n : Nat) : Z0 := ⟨1,[true,true],U (6*n+5)⟩
def outerCost (n : Nat) := 6*(3*n+2)+8+cost 0 (6*n+4)
theorem grow (n : Nat) : run0 table (outerCost n) (family n) = some (family (3*n+2)) := by
  have h1 := prep (3*n+2)
  have h2 := collapse 0 (6*n+4)
  rw [show 2*(3*n+2)+2=6*n+4+2 by omega] at h1
  have H := join0 h1 h2
  simpa only [outerCost,family,show 2*(3*n+2)+1=6*n+5 by omega,show 3*(0+(6*n+4)+1)+2=6*(3*n+2)+5 by omega] using H

def idx : Nat → Nat
  | 0 => 0
  | n+1 => 3*idx n+2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun n => family (idx n)) 20 (fun n => outerCost (idx n)) _ _ _ m hm
  · rfl
  · intro n; unfold outerCost; omega
  · intro n; exact grow (idx n)
#print axioms never
end BB6.Agent19Raw40.Triple32
