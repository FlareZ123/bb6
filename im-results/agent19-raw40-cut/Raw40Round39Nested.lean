import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Round39Nested
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0RD_1RC1LB_0RD0RE_1LD1LA_1LF1RE_---0LB; F0 is unassigned.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def U (n : Nat) := rep [true] n
private theorem uAdd (a b : Nat) : U (a+b) = U a ++ U b := by
  induction a with
  | zero => simp [U,rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega]; simp only [U,rep] at *; rw [ih,List.append_assoc]

def phase (a b : Nat) : Z0 := ⟨1,false::U a,U (2*b)++false::U a⟩
def family (k : Nat) : Z0 := ⟨1,[],U (2*k+4)⟩

theorem start (L R : List Bool) : run0 table 2 ⟨1,false::L,[true,true]++R⟩ =
    some ⟨4,[true,false,true]++L,R⟩ := by rfl

theorem startBlank (R : List Bool) : run0 table 2 ⟨1,[],[true,true]++R⟩ =
    some ⟨4,[true,false,true],R⟩ := by rfl

theorem right (L R : List Bool) : run0 table 1 ⟨4,[true]++L,[true]++R⟩ =
    some ⟨4,[true]++[true]++L,R⟩ := by rfl

theorem turn (L R : List Bool) : run0 table 3 ⟨4,true::L,false::R⟩ =
    some ⟨1,L,false::true::R⟩ := by rfl

theorem turnBlank (L : List Bool) : run0 table 3 ⟨4,true::L,[]⟩ =
    some ⟨1,L,[false,true]⟩ := by rfl

theorem left (L R : List Bool) : run0 table 1 ⟨1,[true]++L,R⟩ =
    some ⟨1,L,[true]++R⟩ := by rfl

theorem epoch (a b : Nat) : run0 table (4*b+5) (phase a (b+1)) = some (phase (a+1) b) := by
  have h1 := start (U a) (U (2*b)++false::U a)
  have h2 := sweepR table 4 [true] [] [true] [true] 1 right (2*b) (false::true::U a) (false::U a)
  have h3 := turn (U (2*b)++false::true::U a) (U a)
  have h4 := sweepL table 1 [] [] [true] [true] 1 left (2*b) (false::true::U a) (false::true::U a)
  simp only [List.nil_append,Nat.one_mul,List.cons_append,List.append_assoc,List.singleton_append] at h2 h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  change run0 table (2+2*b+3+2*b) ⟨1,false::U a,U 2 ++ (U (2*b)++false::U a)⟩ = some (phase (a+1) b) at H
  rw [← List.append_assoc (U 2) (U (2*b)) (false::U a),← uAdd 2 (2*b)] at H
  simpa only [phase,show 2*(b+1)=2+2*b by omega,show 2+2*b+3+2*b=4*b+5 by omega] using H

theorem prep (k : Nat) : run0 table (4*k+9) (family k) = some (phase 1 (k+1)) := by
  have h1 := startBlank (U (2*(k+1)))
  have h2 := sweepR table 4 [true] [] [true] [true] 1 right (2*(k+1)) [false,true] []
  have h3 := turnBlank (U (2*(k+1))++[false,true])
  have h4 := sweepL table 1 [] [] [true] [true] 1 left (2*(k+1)) [false,true] [false,true]
  simp only [List.nil_append,Nat.one_mul,List.append_nil,List.singleton_append] at h2 h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  change run0 table (2+2*(k+1)+3+2*(k+1)) ⟨1,[],U 2 ++ U (2*(k+1))⟩ = some (phase 1 (k+1)) at H
  rw [← uAdd 2 (2*(k+1))] at H
  simpa only [family,show 2*k+4=2+2*(k+1) by omega,show 2+2*(k+1)+3+2*(k+1)=4*k+9 by omega] using H

def collapseCost : Nat → Nat
  | 0 => 0
  | b+1 => 4*b+5+collapseCost b

theorem collapse (a b : Nat) : run0 table (collapseCost b) (phase a b) = some (phase (a+b) 0) := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    simpa only [collapseCost,show a+1+b=a+(b+1) by omega] using join0 (epoch a b) (ih (a+1))

theorem finishStart (L R : List Bool) : run0 table 4 ⟨1,false::L,false::true::R⟩ =
    some ⟨1,[true,true,true]++L,R⟩ := by rfl

theorem finish (a : Nat) : run0 table (a+8) (phase (a+1) 0) = some ⟨1,[],U (2*a+4)⟩ := by
  have h1 := finishStart (U (a+1)) (U a)
  have h2 := sweepL table 1 [] [] [true] [true] 1 left (a+4) [] (U a)
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at h2
  have h1' : run0 table 4 (phase (a+1) 0) = some ⟨1,U (a+4),U a⟩ := by
    rw [show a+4=3+(a+1) by omega,uAdd]
    exact h1
  have H := join0 h1' h2
  change run0 table (4+(a+4)) (phase (a+1) 0) = some ⟨1,[],U (a+4)++U a⟩ at H
  rw [← uAdd] at H
  simpa only [show 4+(a+4)=a+8 by omega,show a+4+a=2*a+4 by omega] using H

def outerCost (k : Nat) := 4*k+9+collapseCost (k+1)+(k+1+8)

theorem grow (k : Nat) : run0 table (outerCost k) (family k) = some (family (k+1)) := by
  have h1 := prep k
  have h2 := collapse 1 (k+1)
  have h3 := finish (k+1)
  rw [show 1+(k+1)=k+1+1 by omega] at h2
  simpa only [outerCost,family] using join0 (join0 h1 h2) h3

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 11 outerCost _ _ grow m hm
  · rfl
  · intro k; unfold outerCost; omega
#print axioms grow
#print axioms never
end BB6.Agent19Raw40.Round39Nested
