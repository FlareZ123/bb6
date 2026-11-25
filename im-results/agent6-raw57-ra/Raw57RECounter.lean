import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6Raw57RE0Pumps.M50
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
abbrev Z : List Bool := [false,false,true]
abbrev O : List Bool := [true,false,true]
abbrev P : List Bool := [true,true,false]

def b (L R : List Bool) : Z0 := ⟨1,false::L,[false,true]++R⟩
def sec (R : List Bool) := b [true] R

def d (L R : List Bool) : Z0 := ⟨3,[false,true]++L,R⟩
def family (n : Nat) : Z0 := ⟨3,Z++rep Z n++[true],[]⟩

theorem bAtom (L R : List Bool) : run0 table 5 (b L (Z++R)) = some (b (Z++L) R) := by rfl

theorem bSweep (k : Nat) (L R : List Bool) :
    run0 table (5*k) (b L (rep Z k++R)) = some (b (rep Z k++L) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (bAtom L (rep Z k++R)) (ih (Z++L))
    rw [show 5*(k+1)=5+5*k by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Z k) Z L,rep_snoc Z k] using h

theorem dAtom (L R : List Bool) : run0 table 9 (d (Z++L) R) = some (d L (P++R)) := by rfl

theorem dSweep (k : Nat) (L R : List Bool) :
    run0 table (9*k) (d (rep Z k++L) R) = some (d L (rep P k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (dAtom (rep Z k++L) R) (ih (P++R))
    rw [show 9*(k+1)=9+9*k by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep P k) P R,rep_snoc P k] using h

theorem dFinish (R : List Bool) : run0 table 7 (d [true] (true::R)) = some (sec R) := by rfl

theorem dFinishAll (k : Nat) (R : List Bool) :
    run0 table 7 (d [true] (rep P k++true::R)) = some (sec (rep O k++R)) := by
  have h : rep P k++[true] = [true]++rep O k := by
    exact (rotate true [true,false] k).symm
  rw [show rep P k++true::R = (rep P k++[true])++R by simp only [List.append_assoc,List.singleton_append],h]
  exact dFinish (rep O k++R)

theorem oneAtom (L R : List Bool) : run0 table 9 (b L (O++R)) = some (d L (true::Z++R)) := by rfl

theorem decrement (k : Nat) (R : List Bool) :
    run0 table (14*k+16) (sec (rep Z k++O++R)) = some (sec (rep O k++Z++R)) := by
  have h1 := bSweep k [true] (O++R)
  have h2 := oneAtom (rep Z k++[true]) R
  have h3 := dSweep k [true] (true::Z++R)
  have h4 := dFinishAll k (Z++R)
  try simp only [List.append_assoc] at h1 h2 h3 h4
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 14*k+16=5*k+9+9*k+7 by omega]
  simpa only [sec,List.append_assoc] using h

def ticks : Nat → Nat
  | 0 => 0
  | k+1 => ticks k + (14*k+16) + ticks k

theorem clear (k : Nat) (R : List Bool) :
    run0 table (ticks k) (sec (rep O k++R)) = some (sec (rep Z k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (O++R)
    have h2 := decrement k R
    have h3 := ih (Z++R)
    simp only [List.append_assoc] at h1 h2 h3
    have h := join0 (join0 h1 h2) h3
    simpa only [ticks,rep,List.append_assoc,← List.append_assoc (rep Z k) Z R,rep_snoc Z k,
      ← List.append_assoc (rep O k) O R,rep_snoc O k] using h

theorem dEntry (k : Nat) : run0 table 1 (family k) = some (d (rep Z k++[true]) [true]) := by rfl

theorem init (k : Nat) : run0 table (9*k+8) (family k) = some (sec (rep O k)) := by
  have h := join0 (join0 (dEntry k) (dSweep k [true] [true])) (dFinishAll k [])
  rw [show 9*k+8=1+9*k+7 by omega]
  simpa using h

theorem overflowAtom (L : List Bool) : run0 table 7 (b L []) = some ⟨3,Z++Z++L,[]⟩ := by rfl

theorem overflow (k : Nat) : run0 table (5*k+7) (sec (rep Z k)) = some (family (k+1)) := by
  have h := join0 (bSweep k [true] []) (overflowAtom (rep Z k++[true]))
  simpa only [sec,List.append_nil,family,rep,List.append_assoc] using h

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table ((9*n+8)+ticks n+(5*n+7)) (family n) = some (family (n+1)) := by
  have h := clear n []
  simp only [List.append_nil] at h
  exact join0 (join0 (init n) h) (overflow n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => (9*n+8)+ticks n+(5*n+7)) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent6Raw57RE0Pumps.M50
