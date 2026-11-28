import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent36Raw41Child094Leaf66
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def X : List Bool := [true,false,true,false]
def Y : List Bool := [false,true,false,true]
def U (m : Nat) := rep [true] m ++ [false,false,true,true]
def evenR : Nat → List Bool
  | 0 => [false]
  | j+1 => [false] ++ rep X j ++ [true,false,true]
def oddR (j : Nat) := [false] ++ rep X j ++ [true,true]
def Outer (n : Nat) : Z0 := ⟨5,[false,false,false,true,true],rep P n ++ [true,true]⟩
def E (m j : Nat) : Z0 := ⟨5,[false,false]++U m,evenR j⟩
def O (m j : Nat) : Z0 := ⟨5,[false,false]++U m,oddR j⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (Outer 0) := by rfl

theorem cSweep (L R : List Bool) : run0 table 4 ⟨2,[true,true]++L,Q++R⟩ = some ⟨2,[true,true]++[true,true]++L,R⟩ := by rfl
theorem cEnd (L : List Bool) : run0 table 7 ⟨2,[true,true]++L,[true]⟩ = some ⟨5,[false,false,true]++L,[false]⟩ := by rfl
theorem fSweep (L R : List Bool) : run0 table 8 ⟨5,[false,false]++L,[false]++X++R⟩ = some ⟨5,[false,false]++X++L,[false]++R⟩ := by rfl
theorem fLast (L : List Bool) : run0 table 8 ⟨5,[false,false]++L,[false,true,false,true]⟩ = some ⟨5,[false,false]++X++L,[false]⟩ := by rfl
theorem fEven (L : List Bool) : run0 table 5 ⟨5,[false,false]++L,[false]⟩ = some ⟨0,[true,true,false]++L,[true]⟩ := by rfl
theorem fOdd (L : List Bool) : run0 table 3 ⟨5,[false,false]++L,[false,true,true]⟩ = some ⟨0,[true,true,false]++P++L,[]⟩ := by rfl
theorem aPair (L R : List Bool) : run0 table 4 ⟨0,[true,true,false]++P++L,R⟩ = some ⟨0,[true,true,false]++L,Q++R⟩ := by rfl
theorem aSweep (L R : List Bool) : run0 table 8 ⟨0,[true,true,false]++X++L,R⟩ = some ⟨0,[true,true,false]++L,Y++R⟩ := by rfl
theorem aEnd (L R : List Bool) : run0 table 12 ⟨0,[true,true,false,true,true]++L,R⟩ = some ⟨5,[false,false,true]++L,Q++R⟩ := by rfl
theorem aTerminal (R : List Bool) : run0 table 15 ⟨0,[true,true,false,true,false,false,true,true],R⟩ = some ⟨5,[false,false,false,true,true],[true,false,true]++R⟩ := by rfl

theorem repTwo (n : Nat) : rep [true,true] n = rep [true] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp [rep, ih]

theorem outStart (n : Nat) : run0 table (4*n+8) (Outer n) = some (E (2*n+1) 0) := by
  have hrot : [true] ++ rep Q n = rep P n ++ [true] := rotate true [false] n
  have h0 : run0 table 1 (Outer n) = some ⟨2,[true,true,false,false,true,true],rep Q n ++ [true]⟩ := by
    unfold Outer
    have hr : rep P n ++ [true,true] = [true] ++ (rep Q n ++ [true]) := by
      rw [← List.append_assoc, hrot, List.append_assoc]
      rfl
    rw [hr]
    rfl
  have h1 := sweepR table 2 [true,true] [] Q [true,true] 4 cSweep n [false,false,true,true] [true]
  have h2 := cEnd (rep [true,true] n ++ [false,false,true,true])
  have h := join0 (join0 h0 h1) h2
  rw [repTwo, show 1+4*n+7=4*n+8 by omega] at h
  simpa [E,U,evenR,rep,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem commuteQ (j : Nat) : Q ++ rep Y j = rep Y j ++ Q := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change Q ++ (Y ++ rep Y j) = (Y ++ rep Y j) ++ Q
    rw [← List.append_assoc, show Q ++ Y = Y ++ Q by rfl, List.append_assoc, ih, ← List.append_assoc]

theorem oddForm (j : Nat) : oddR j = Q ++ rep Y j ++ [true] := by
  have h : [false] ++ rep X j = rep Y j ++ [false] := rotate false [true,false,true] j
  unfold oddR
  rw [h, commuteQ]
  simp only [List.append_assoc]
  rfl

theorem evenForm (j : Nat) : evenR (j+1) = Q ++ rep Y j ++ Q := by
  have h : [false] ++ rep X j = rep Y j ++ [false] := rotate false [true,false,true] j
  change [false] ++ rep X j ++ [true,false,true] = _
  rw [h, commuteQ]
  simp only [List.append_assoc]
  rfl

theorem evenToA (m j : Nat) : run0 table (16*j+5) (E m j) = some ⟨0,[true,true,false]++U m,rep Y j ++ [true]⟩ := by
  cases j with
  | zero => exact fEven (U m)
  | succ j =>
    have h0 := sweepR table 5 [false,false] [false] X X 8 fSweep j (U m) [true,false,true]
    have h1 := fLast (rep X j ++ U m)
    have h2 := fEven (X ++ rep X j ++ U m)
    have h3 := sweepL table 0 [true,true,false] [] X Y 8 aSweep (j+1) (U m) [true]
    have h := join0 (join0 (join0 h0 h1) h2) h3
    rw [show 8*j+8+5+8*(j+1)=16*(j+1)+5 by omega] at h
    simpa [E,evenR,rep,List.append_assoc,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem oddToA (m j : Nat) : run0 table (16*j+7) (O m j) = some ⟨0,[true,true,false]++U m,rep Y j ++ Q⟩ := by
  have h0 := sweepR table 5 [false,false] [false] X X 8 fSweep j (U m) [true,true]
  have h1 := fOdd (rep X j ++ U m)
  have h2 := aPair (rep X j ++ U m) []
  have h3 := sweepL table 0 [true,true,false] [] X Y 8 aSweep j (U m) Q
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 8*j+3+4+8*j=16*j+7 by omega] at h
  simpa [O,oddR,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem evenStep (m j : Nat) : run0 table (16*j+17) (E (m+2) j) = some (O (m+1) j) := by
  have h0 := evenToA (m+2) j
  have h1 := aEnd (U m) (rep Y j ++ [true])
  have h := join0 h0 h1
  simpa [U,O,rep,oddForm,List.append_assoc,Nat.add_assoc] using h

theorem oddStep (m j : Nat) : run0 table (16*j+19) (O (m+2) j) = some (E (m+1) (j+1)) := by
  have h0 := oddToA (m+2) j
  have h1 := aEnd (U m) (rep Y j ++ Q)
  have h := join0 h0 h1
  simpa [U,E,rep,evenForm,List.append_assoc,Nat.add_assoc] using h

theorem terminalR (j : Nat) : [true,false,true] ++ (rep Y j ++ [true]) = rep P (2*j+1) ++ [true,true] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)+1 = (2*j+1)+1+1 by omega]
    simp only [rep] at ih ⊢
    change X ++ ([true,false,true] ++ (rep Y j ++ [true])) = X ++ (rep P (2*j+1) ++ [true,true])
    rw [ih]
    rfl

theorem terminal (j : Nat) : run0 table (16*j+20) (E 1 j) = some (Outer (2*j+1)) := by
  have h0 := evenToA 1 j
  have h1 := aTerminal (rep Y j ++ [true])
  have h := join0 h0 h1
  rw [show 16*j+5+15=16*j+20 by omega] at h
  unfold Outer
  rw [← terminalR]
  exact h

def pairCost : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,j => 32*j+36+pairCost k (j+1)

theorem pairCost_eq (k j : Nat) : pairCost k j = 16*k*k+20*k+32*k*j := by
  induction k generalizing j with
  | zero => simp [pairCost]
  | succ k ih =>
    simp only [pairCost,ih,Nat.add_mul,Nat.mul_add]
    omega

theorem drain (k j : Nat) : run0 table (pairCost k j) (E (2*k+1) j) = some (E 1 (j+k)) := by
  induction k generalizing j with
  | zero => simp [pairCost,run0]
  | succ k ih =>
    have h0 := evenStep (2*k+1) j
    have h1 := oddStep (2*k) j
    have h2 := ih (j+1)
    have h := join0 (join0 h0 h1) h2
    rw [show 16*j+17+(16*j+19)+pairCost k (j+1) = pairCost (k+1) j by simp [pairCost]; omega] at h
    rw [show 2*(k+1)+1 = 2*k+1+2 by omega,show j+(k+1) = j+1+k by omega]
    exact h

theorem outerStep (n : Nat) : run0 table (16*n*n+40*n+28) (Outer n) = some (Outer (2*n+1)) := by
  have h0 := outStart n
  have h1 := drain n 0
  have h2 := terminal n
  simp only [Nat.zero_add] at h1
  have h := join0 (join0 h0 h1) h2
  rw [pairCost_eq] at h
  rw [show 4*n+8+(16*n*n+20*n+32*n*0)+(16*n+20)=16*n*n+40*n+28 by omega] at h
  exact h

def orbit : Nat → Nat
  | 0 => 0
  | k+1 => 2*orbit k+1

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun k => Outer (orbit k)) 28 (fun k => 16*orbit k*orbit k+40*orbit k+28) entry
  · intro k; omega
  · intro k; exact outerStep (orbit k)
  · exact hm
#print axioms never
end BB6.Agent36Raw41Child094Leaf66
