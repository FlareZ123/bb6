import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent36Raw41Child112Single
open BB6Coverage BB6Coverage.Agent31Pump

def table (b : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if b then some (some ⟨true,true,2⟩) else some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def I := [true]
def Z := [false]
def S (b : Bool) := if b then [true,true,true,false,true,true,true,false] else [true,true,true,false]
def base (b : Bool) : Nat := if b then 3 else 1
def Cprefix (b : Bool) := if b then [true,false,false,false,true,true] else [true,false,false,true]
def Cleft (b : Bool) := if b then [false,true,true,true,false] else [false]
def Counter (b : Bool) (R : List Bool) : Z0 := ⟨2,Cleft b,Cprefix b++R⟩
def Outer (b : Bool) (n : Nat) : Z0 := ⟨5,rep Z (n+base b)++S b,I⟩
def decodeCost (b : Bool) : Nat := if b then 31 else 7

theorem fOne (b : Bool) (L R : List Bool) : run0 (table b) 1 ⟨5,Z++L,R⟩ = some ⟨5,L,Z++R⟩ := by cases b <;> rfl
theorem eOne (b : Bool) (L R : List Bool) : run0 (table b) 1 ⟨4,I++L,I++R⟩ = some ⟨4,I++Z++L,R⟩ := by cases b <;> rfl
theorem eZero (b : Bool) (L R : List Bool) : run0 (table b) 2 ⟨4,I++L,Z++R⟩ = some ⟨5,Z++L,I++R⟩ := by cases b <;> rfl
theorem eBlank (b : Bool) (L : List Bool) : run0 (table b) 2 ⟨4,I++L,[]⟩ = some ⟨5,Z++L,I⟩ := by cases b <;> rfl
theorem decode (b : Bool) (R : List Bool) : run0 (table b) (decodeCost b) ⟨5,S b,rep Z (base b)++R⟩ = some (Counter b R) := by cases b <;> rfl
theorem startC (R : List Bool) : run0 (table false) 4 (Counter false R) = some ⟨2,[true,true,true,true,false],R⟩ := by rfl
theorem cToE (R : List Bool) : run0 (table false) 1 ⟨2,[true,true,true,true,false],I++R⟩ = some ⟨4,I++Z++S false,R⟩ := by rfl
theorem cZero (R : List Bool) : run0 (table false) 2 ⟨2,[true,true,true,true,false],Z++R⟩ = some ⟨5,Z++S false,I++R⟩ := by rfl
theorem cBlank : run0 (table false) 2 ⟨2,[true,true,true,true,false],[]⟩ = some ⟨5,Z++S false,I⟩ := by rfl
theorem startE (R : List Bool) : run0 (table true) 8 (Counter true R) = some ⟨4,I++Z++Z++S true,R⟩ := by rfl

theorem repJoin (xs : List Bool) (m n : Nat) : rep xs m++rep xs n = rep xs (m+n) := by
  induction m with
  | zero => simp [rep]
  | succ m ih => simp only [rep,List.append_assoc,ih,show m+1+n=m+n+1 by omega]

theorem carryFront (b : Bool) (k : Nat) (R : List Bool) :
    run0 (table b) ((if b then 10 else 6)+k) (Counter b (rep I k++Z++R)) = some ⟨5,rep Z (k+base b)++S b,I++R⟩ := by
  cases b with
  | false =>
    have h0 := startC (rep I k++Z++R)
    cases k with
    | zero =>
      have h := join0 h0 (cZero R)
      exact h
    | succ k =>
      have h1 := cToE (rep I k++Z++R)
      have h2 := sweepR (table false) 4 I [] I Z 1 (eOne false) k (Z++S false) (Z++R)
      have h3 := eZero false (rep Z k++Z++S false) R
      simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3
      have h := join0 (join0 (join0 h0 h1) h2) h3
      rw [show 4+1+1*k+2=6+(k+1) by omega] at h
      have hz : rep Z k++Z = Z++rep Z k := rep_snoc Z k
      simpa [base,rep,List.append_assoc,← hz] using h
  | true =>
    have h0 := startE (rep I k++Z++R)
    have h1 := sweepR (table true) 4 I [] I Z 1 (eOne true) k (Z++Z++S true) (Z++R)
    have h2 := eZero true (rep Z k++Z++Z++S true) R
    simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2
    have h := join0 (join0 h0 h1) h2
    rw [show 8+1*k+2=10+k by omega] at h
    have hzr : rep Z k++rep Z 2 = rep Z (k+2) := repJoin Z k 2
    have hz : rep Z k++(Z++Z) = rep Z (k+2) := hzr
    have hzz : rep Z k++(Z++(Z++S true)) = rep Z (k+2)++S true := by
      rw [← List.append_assoc Z Z (S true),← List.append_assoc,hz]
    rw [hzz] at h
    simpa [base,rep,List.append_assoc] using h

theorem carry (b : Bool) (k : Nat) (R : List Bool) :
    run0 (table b) ((if b then 44 else 14)+2*k) (Counter b (rep I k++Z++R)) = some (Counter b (rep Z k++I++R)) := by
  have h0 := carryFront b k R
  have h1 := sweepL (table b) 5 [] [] Z Z 1 (fOne b) (k+base b) (S b) (I++R)
  have h2 := decode b (rep Z k++I++R)
  have hz : rep Z (k+base b) = rep Z (base b)++rep Z k := by rw [repJoin,Nat.add_comm]
  rw [hz] at h1
  rw [hz] at h0
  simp only [List.append_assoc,List.nil_append] at h0 h1 h2
  have h := join0 (join0 h0 h1) h2
  cases b <;> simp [base,decodeCost] at h ⊢
  · rw [show 6+k+(k+1)+7=14+2*k by omega] at h; exact h
  · rw [show 10+k+(k+3)+31=44+2*k by omega] at h; exact h

def countCost (b : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => countCost b n + ((if b then 44 else 14)+2*n) + countCost b n

theorem count (b : Bool) (n : Nat) (R : List Bool) :
    run0 (table b) (countCost b n) (Counter b (rep Z n++R)) = some (Counter b (rep I n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h0 := ih (Z++R)
    have h1 := carry b n R
    have h2 := ih (I++R)
    simp only [List.append_assoc] at h1
    have h := join0 (join0 h0 h1) h2
    have hz : rep Z (n+1) = rep Z n++Z := (rep_snoc Z n).symm
    have hi : rep I (n+1) = rep I n++I := (rep_snoc I n).symm
    rw [hz,hi]
    simpa [countCost,List.append_assoc] using h

theorem finish (b : Bool) (k : Nat) :
    run0 (table b) ((if b then 10 else 6)+k) (Counter b (rep I k)) = some ⟨5,rep Z (k+base b)++S b,I⟩ := by
  cases b with
  | false =>
    have h0 := startC (rep I k)
    cases k with
    | zero =>
      have h := join0 h0 cBlank
      exact h
    | succ k =>
      have h1 := cToE (rep I k)
      have h2 := sweepR (table false) 4 I [] I Z 1 (eOne false) k (Z++S false) []
      have h3 := eBlank false (rep Z k++Z++S false)
      simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3
      have h := join0 (join0 (join0 h0 h1) h2) h3
      rw [show 4+1+1*k+2=6+(k+1) by omega] at h
      have hz : rep Z k++Z = Z++rep Z k := rep_snoc Z k
      simpa [base,rep,List.append_assoc,← hz] using h
  | true =>
    have h0 := startE (rep I k)
    have h1 := sweepR (table true) 4 I [] I Z 1 (eOne true) k (Z++Z++S true) []
    have h2 := eBlank true (rep Z k++Z++Z++S true)
    simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2
    have h := join0 (join0 h0 h1) h2
    rw [show 8+1*k+2=10+k by omega] at h
    have hzr : rep Z k++rep Z 2 = rep Z (k+2) := repJoin Z k 2
    have hz : rep Z k++(Z++Z) = rep Z (k+2) := hzr
    have hzz : rep Z k++(Z++(Z++S true)) = rep Z (k+2)++S true := by
      rw [← List.append_assoc Z Z (S true),← List.append_assoc,hz]
    rw [hzz] at h
    simpa [base,rep,List.append_assoc] using h

def growthCost (b : Bool) (n : Nat) := n+base b+decodeCost b+countCost b n+((if b then 10 else 6)+(n+1))

theorem growth (b : Bool) (n : Nat) : run0 (table b) (growthCost b n) (Outer b n) = some (Outer b (n+1)) := by
  have h0 := sweepL (table b) 5 [] [] Z Z 1 (fOne b) (n+base b) (S b) I
  have h1 := decode b (rep Z n++I)
  have hz : rep Z (n+base b) = rep Z (base b)++rep Z n := by rw [repJoin,Nat.add_comm]
  rw [hz] at h0
  simp only [List.append_assoc,List.nil_append] at h0 h1
  have h2 := count b n I
  have h3 := finish b (n+1)
  have hi : rep I (n+1) = rep I n++I := (rep_snoc I n).symm
  rw [hi] at h3
  have h := join0 (join0 (join0 h0 h1) h2) h3
  unfold Outer growthCost
  rw [hz]
  simpa [List.append_assoc,Nat.add_assoc] using h

def startN (b : Bool) : Nat := if b then 0 else 6
def entryCost (b : Bool) : Nat := if b then 61 else 485

theorem entry (b : Bool) : run0 (table b) (entryCost b) ⟨0,[],[]⟩ = some (Outer b (startN b)) := by cases b <;> rfl

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m := by
  apply never_of_growth (table b) (fun n => Outer b (startN b+n)) (entryCost b) (fun n => growthCost b (startN b+n)) (by simpa using entry b)
  · intro n; unfold growthCost; cases b <;> simp [base,decodeCost] <;> omega
  · intro n; simpa [Nat.add_assoc] using growth b (startN b+n)
  · exact hm
#print axioms never
end BB6.Agent36Raw41Child112Single
