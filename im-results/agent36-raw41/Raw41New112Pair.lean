import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent36Raw41Child112Pair
open BB6Coverage BB6Coverage.Agent31Pump

def table (b : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if b then some (some ⟨true,true,1⟩) else some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def I := [true]
def Z := [false]
def I4 := [true,true,true,true]
def Z4 := [false,false,false,false]
def Counter (R : List Bool) : Z0 := ⟨0,[false,false],R⟩
def Start (n : Nat) : Z0 := ⟨2,[false,true] ++ rep I (4*n+5) ++ [false],[]⟩
def entryCost (b : Bool) : Nat := if b then 28 else 36

theorem entry (b : Bool) : run0 (table b) (entryCost b) ⟨0,[],[]⟩ = some (Start 0) := by cases b <;> rfl

theorem initF (b : Bool) (L : List Bool) : run0 (table b) 18 ⟨2,[false,true]++L,[]⟩ = some ⟨5,L,I4⟩ := by cases b <;> rfl
theorem fOne (b : Bool) (L R : List Bool) : run0 (table b) 1 ⟨5,I++L,R⟩ = some ⟨5,L,Z++R⟩ := by cases b <;> rfl
theorem fEnd (b : Bool) (R : List Bool) : run0 (table b) 1 ⟨5,[false],Z++R⟩ = some (Counter R) := by cases b <;> rfl
theorem aOne (L R : List Bool) : run0 (table false) 3 ⟨0,Z++L,I++R⟩ = some ⟨0,Z++I++L,R⟩ := by rfl
theorem aStartB (L R : List Bool) : run0 (table true) 1 ⟨0,Z++L,I++R⟩ = some ⟨1,[true,true]++L,R⟩ := by rfl
theorem bOne (L R : List Bool) : run0 (table true) 1 ⟨1,I++L,I++R⟩ = some ⟨1,I++I++L,R⟩ := by rfl
theorem bZero (L R : List Bool) : run0 (table true) 1 ⟨1,I++L,Z++R⟩ = some ⟨1,[false,true]++L,R⟩ := by rfl
theorem bBlank (L : List Bool) : run0 (table true) 1 ⟨1,I++L,[]⟩ = some ⟨1,[false,true]++L,[]⟩ := by rfl
theorem aCarry (b : Bool) (L R : List Bool) : run0 (table b) 20 ⟨0,Z++L,Z4++R⟩ = some ⟨5,I++L,I4++R⟩ := by cases b <;> rfl
theorem bCarry (L R : List Bool) : run0 (table true) 19 ⟨1,[false,true]++L,[false,false,false]++R⟩ = some ⟨5,I++L,I4++R⟩ := by rfl
theorem aFinish (b : Bool) (L : List Bool) : run0 (table b) 2 ⟨0,Z++L,[]⟩ = some ⟨2,[false,true,true]++L,[]⟩ := by cases b <;> rfl
theorem bFinish (L : List Bool) : run0 (table true) 1 ⟨1,[false,true]++L,[]⟩ = some ⟨2,[false,true,true]++L,[]⟩ := by rfl

theorem rep4 (v : Bool) (n : Nat) : rep [v,v,v,v] n = rep [v] (4*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
    simp [rep,ih]

def scanCost (b : Bool) (k : Nat) := if b then k else 3*k

theorem carryFront (b : Bool) (k : Nat) (L R : List Bool) :
    run0 (table b) (scanCost b k+20) ⟨0,Z++L,rep I k++Z4++R⟩ = some ⟨5,I++rep I k++L,I4++R⟩ := by
  cases b with
  | false =>
    have h0 := sweepR (table false) 0 Z [] I I 3 aOne k L (Z4++R)
    have h1 := aCarry false (rep I k++L) R
    have h := join0 h0 h1
    simpa [scanCost,List.append_assoc] using h
  | true =>
    cases k with
    | zero => exact aCarry true L R
    | succ k =>
      have h0 := aStartB L (rep I k++Z4++R)
      have h1 := sweepR (table true) 1 I [] I I 1 bOne k (I++L) (Z4++R)
      have h2 := bZero (rep I k++(I++L)) ([false,false,false]++R)
      have h3 := bCarry (rep I k++(I++L)) R
      simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3
      have h := join0 (join0 (join0 h0 h1) h2) h3
      rw [show 1+1*k+1+19=(k+1)+20 by omega] at h
      have hr : rep I k++I = I++rep I k := rep_snoc I k
      rw [← List.append_assoc (rep I k) I L,hr] at h
      simpa [scanCost,rep,List.append_assoc] using h

theorem carry (b : Bool) (n : Nat) (R : List Bool) :
    run0 (table b) (scanCost b (4*n)+4*n+22) (Counter (rep I4 n++Z4++R)) = some (Counter (rep Z4 n++I4++R)) := by
  have h0 := carryFront b (4*n) [false] R
  have h1 := sweepL (table b) 5 [] [] I Z 1 (fOne b) (4*n+1) [false] (I4++R)
  have h2 := fEnd b (rep Z (4*n)++I4++R)
  have h2' : run0 (table b) 1 ⟨5,[false],rep Z (4*n+1)++(I4++R)⟩ = some (Counter (rep Z (4*n)++I4++R)) := by
    simpa only [rep,List.append_assoc] using h2
  have h := join0 (join0 h0 h1) h2'
  rw [show scanCost b (4*n)+20+1*(4*n+1)+1=scanCost b (4*n)+4*n+22 by omega] at h
  have hi : rep I4 n = rep I (4*n) := rep4 true n
  have hz : rep Z4 n = rep Z (4*n) := rep4 false n
  rw [hi,hz]
  exact h

def countCost (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => countCost b n + (scanCost b (4*n)+4*n+22) + countCost b n

theorem count (b : Bool) (n : Nat) (R : List Bool) :
    run0 (table b) (countCost b n) (Counter (rep Z4 n++R)) = some (Counter (rep I4 n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h0 := ih (Z4++R)
    have h1 := carry b n R
    have h2 := ih (I4++R)
    simp only [List.append_assoc] at h1
    have h := join0 (join0 h0 h1) h2
    have hz : rep Z4 (n+1) = rep Z4 n++Z4 := (rep_snoc Z4 n).symm
    have hi : rep I4 (n+1) = rep I4 n++I4 := (rep_snoc I4 n).symm
    rw [hz,hi]
    simpa [countCost,List.append_assoc] using h

theorem finish (b : Bool) (k : Nat) (L : List Bool) :
    run0 (table b) (scanCost b k+2) ⟨0,Z++L,rep I k⟩ = some ⟨2,[false,true,true]++rep I k++L,[]⟩ := by
  cases b with
  | false =>
    have h0 := sweepR (table false) 0 Z [] I I 3 aOne k L []
    have h1 := aFinish false (rep I k++L)
    have h := join0 h0 h1
    simpa [scanCost,List.append_assoc] using h
  | true =>
    cases k with
    | zero => exact aFinish true L
    | succ k =>
      have h0 := aStartB L (rep I k)
      have h1 := sweepR (table true) 1 I [] I I 1 bOne k (I++L) []
      have h2 := bBlank (rep I k++(I++L))
      have h3 := bFinish (rep I k++(I++L))
      simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3
      have h := join0 (join0 (join0 h0 h1) h2) h3
      rw [show 1+1*k+1+1=(k+1)+2 by omega] at h
      have hr : rep I k++I = I++rep I k := rep_snoc I k
      rw [← List.append_assoc (rep I k) I L,hr] at h
      simpa [scanCost,rep,List.append_assoc] using h

def growthCost (b : Bool) (n : Nat) := 18+(4*n+5)+1+countCost b (n+1)+scanCost b (4*(n+2))+2

theorem growth (b : Bool) (n : Nat) : run0 (table b) (growthCost b n) (Start n) = some (Start (n+1)) := by
  have h0 := initF b (rep I (4*n+5)++[false])
  have h1 := sweepL (table b) 5 [] [] I Z 1 (fOne b) (4*n+5) [false] I4
  have h2 := fEnd b (rep Z (4*n+4)++I4)
  have h01 := join0 (join0 h0 h1) h2
  have hz : rep Z4 (n+1) = rep Z (4*n+4) := by simpa [Z4,Z,Nat.mul_succ] using rep4 false (n+1)
  have h3 := count b (n+1) I4
  rw [hz] at h3
  have h4 := finish b (4*(n+2)) [false]
  have hi : rep I (4*(n+2)) = rep I4 (n+1)++I4 := by
    change rep [true] (4*(n+2)) = _
    rw [← rep4 true (n+2)]
    exact (rep_snoc I4 (n+1)).symm
  rw [hi] at h4
  have h := join0 (join0 h01 h3) h4
  rw [← hi] at h
  unfold Start
  rw [show 4*(n+1)+5=4*(n+2)+1 by omega]
  simpa [growthCost,rep,I,List.append_assoc,Nat.add_assoc] using h

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m := by
  apply never_of_growth (table b) Start (entryCost b) (growthCost b) (entry b)
  · intro n; unfold growthCost; omega
  · exact growth b
  · exact hm
#print axioms never
end BB6.Agent36Raw41Child112Pair
