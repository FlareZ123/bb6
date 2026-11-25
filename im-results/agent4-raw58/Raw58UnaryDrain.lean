import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4UnaryDrain
open BB6Coverage Agent31Pump
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,if v then 1 else 0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v then none else some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if v then some (some ⟨true,false,5⟩) else none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def ones (n : Nat) := rep [true] n
def zeros (n : Nat) := rep [false] n
def A (n : Nat) : Z0 := ⟨0,[false,false]++ones n,[]⟩
def E (a b : Nat) : Z0 := ⟨4,[],zeros a++ones b⟩
theorem repAdd (x : List Bool) (a b : Nat) : rep x (a+b) = rep x a ++ rep x b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega]; simp only [rep,ih,List.append_assoc]
theorem onesAdd (a b : Nat) : ones (a+b) = ones a ++ ones b := repAdd _ _ _
theorem zerosAdd (a b : Nat) : zeros (a+b) = zeros a ++ zeros b := repAdd _ _ _
theorem aStart (v : Bool) (n : Nat) : run0 (table v) 15 (A (n+1)) = some ⟨0,[false,false]++ones n,[false,false,false,true]⟩ := by cases v <;> rfl
theorem aSweep (v : Bool) (n : Nat) : run0 (table v) (15*n) ⟨0,[false,false]++ones n,[false,false,false,true]⟩ = some ⟨0,[false,false],[false,false,false]++ones (n+1)⟩ := by
  have h := sweepL (table v) 0 [false,false] [false,false,false] [true] [true] 15 (by intro L R; cases v <;> rfl) n [] [true]
  simpa only [ones,rep_snoc,rep,List.append_nil,List.cons_append,List.nil_append,List.append_assoc] using h
theorem aEnd (v : Bool) (n : Nat) : run0 (table v) 14 ⟨0,[false,false],[false,false,false]++ones (n+1)⟩ = some (E 4 (n+2)) := by cases v <;> rfl
theorem aReturn (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (A (n+1)) = some (E 4 (n+2)) :=
  ⟨15+15*n+14,by omega,join0 (join0 (aStart v n) (aSweep v n)) (aEnd v n)⟩
theorem eSweep (v : Bool) (a b : Nat) : run0 (table v) (a+1) (E (a+1) b) = some ⟨4,[false]++ones (a+1),ones b⟩ := by
  have h1 : run0 (table v) 1 (E (a+1) b) = some ⟨4,[false,true],zeros a++ones b⟩ := by cases v <;> rfl
  have h2 := sweepR (table v) 4 [false] [] [false] [true] 1 (by intro L R; cases v <;> rfl) a [true] (ones b)
  have h3 : run0 (table v) a ⟨4,[false,true],zeros a++ones b⟩ = some ⟨4,[false]++ones (a+1),ones b⟩ := by
    simpa only [Nat.one_mul,ones,zeros,rep_snoc,rep,List.nil_append,List.cons_append,List.append_assoc] using h2
  simpa only [Nat.add_comm 1 a] using join0 h1 h3
theorem eLast (v : Bool) (a : Nat) : run0 (table v) 2 ⟨4,[false]++ones (a+1),ones 1⟩ = some (A (a+2)) := by cases v <;> rfl
theorem fStart (v : Bool) (a b : Nat) : run0 (table v) 5 ⟨4,[false]++ones (a+1),ones (b+2)⟩ = some ⟨5,ones (a+3),ones (b+1)⟩ := by cases v <;> rfl
theorem fSweep (v : Bool) (a b : Nat) : run0 (table v) (a+3) ⟨5,ones (a+3),ones (b+1)⟩ = some ⟨5,[],zeros (a+3)++ones (b+1)⟩ := by
  have h := sweepL (table v) 5 [] [] [true] [false] 1 (by intro L R; cases v <;> rfl) (a+3) [] (ones (b+1))
  simpa only [Nat.one_mul,ones,zeros,List.nil_append,List.append_nil] using h
theorem fEnd (v : Bool) (a b : Nat) : run0 (table v) 1 ⟨5,[],zeros (a+3)++ones (b+1)⟩ = some (E (a+4) (b+1)) := by cases v <;> rfl
theorem eReduce (v : Bool) (a b : Nat) : ∃ t, 0<t ∧ run0 (table v) t (E (a+1) (b+2)) = some (E (a+4) (b+1)) :=
  ⟨a+1+5+(a+3)+1,by omega,join0 (join0 (join0 (eSweep v a (b+2)) (fStart v a b)) (fSweep v a b)) (fEnd v a b)⟩
theorem eReturn (v : Bool) (a b : Nat) : ∃ t, 0<t ∧ run0 (table v) t (E (a+1) (b+1)) = some (A (a+3*b+2)) := by
  induction b generalizing a with
  | zero => exact ⟨a+1+2,by omega,by simpa using join0 (eSweep v a 1) (eLast v a)⟩
  | succ b ih =>
    obtain ⟨t,ht,h1⟩ := eReduce v a b
    obtain ⟨u,hu,h2⟩ := ih (a+3)
    rw [show a+3+3*b+2=a+3*(b+1)+2 by omega] at h2
    exact ⟨t+u,by omega,join0 h1 h2⟩
theorem grow (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (A (n+1)) = some (A (3*n+8)) := by
  obtain ⟨t,ht,h1⟩ := aReturn v n
  obtain ⟨u,hu,h2⟩ := eReturn v 3 (n+1)
  rw [show 3+3*(n+1)+2=3*n+8 by omega] at h2
  exact ⟨t+u,by omega,join0 h1 h2⟩
theorem arbitrary (v : Bool) (k : Nat) : ∃ t n, k≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (A (n+1)) := by
  induction k with
  | zero => exact ⟨20,4,by decide,by cases v <;> rfl⟩
  | succ k ih =>
    obtain ⟨t,n,ht,hh⟩ := ih
    obtain ⟨u,hu,hg⟩ := grow v n
    exact ⟨t+u,3*n+7,by omega,join0 hh hg⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  Agent4Live.never_of_live (table v) (fun n => by
    obtain ⟨t,k,ht,hr⟩ := arbitrary v n
    exact ⟨t,A (k+1),ht,hr⟩) m hm
namespace M3780
abbrev table := Agent4UnaryDrain.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4UnaryDrain.never true m hm
end M3780
namespace M3298
abbrev table := Agent4UnaryDrain.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4UnaryDrain.never false m hm
end M3298
#print axioms never
end BB6Coverage.Agent4UnaryDrain
