import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6Raw57RAPumps.M28
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev TT : List Bool := [true,true]
abbrev FT : List Bool := [false,true]
abbrev FF : List Bool := [false,false]

-- The parameter n counts pairs beyond the first pair of ones.
def D (n : Nat) : Z0 := ⟨3,FF++TT++rep TT n++FF,[]⟩
def K (w : List Bool) : Z0 := ⟨0,[true,false],[false]++w++[false]⟩
def B (l w : List Bool) : Z0 := ⟨1,w.headD false::l,w.tail⟩

theorem pre (w : List Bool) : run0 table 2 (K w) = some (B [true,false,false] (w++[false])) := by rfl

theorem carryAtom (L R : List Bool) : run0 table 2 (B L (FT++R)) = some (B (TT++L) R) := by rfl

theorem carry (k : Nat) (L R : List Bool) :
    run0 table (2*k) (B L (rep FT k++R)) = some (B (rep TT k++L) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (carryAtom L (rep FT k++R)) (ih (TT++L))
    rw [show 2*(k+1)=2+2*k by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep TT k) TT L,rep_snoc TT k] using h

theorem fAtom (L R : List Bool) :
    run0 table 2 ⟨5,TT++L,R⟩ = some ⟨5,L,TT++R⟩ := by rfl

theorem fSweep (k : Nat) (R : List Bool) :
    run0 table (2*k) ⟨5,rep TT k++[true,false,false],R⟩ =
      some ⟨5,[true,false,false],rep TT k++R⟩ := by
  simpa using sweepL table 5 [] [] TT TT 2 fAtom k [true,false,false] R

theorem fFinish (R : List Bool) : run0 table 5 ⟨5,[true,false,false],R⟩ =
    some ⟨0,[true,false],false::R⟩ := by rfl

theorem eraseFirst (k : Nat) (R : List Bool) :
    run0 table 1 (B (rep TT k++[true,false,false]) (TT++R)) =
      some ⟨5,rep TT k++[true,false,false],FT++R⟩ := by rfl

-- Subtract one from a little-endian binary word whose digits are 01 and 11.
theorem decr (k : Nat) (R : List Bool) :
    run0 table (4*k+8) (K (rep FT k++TT++R)) =
      some (K (rep TT k++FT++R)) := by
  have h1 := pre (rep FT k++TT++R)
  have h2 := carry k [true,false,false] (TT++R++[false])
  have h3 := eraseFirst k (R++[false])
  have h4 := fSweep k (FT++R++[false])
  have h5 := fFinish (rep TT k++FT++R++[false])
  simp only [List.append_assoc] at h1 h2 h3 h4 h5
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 4*k+8=2+2*k+1+2*k+5 by omega]
  simpa only [K,List.append_assoc,List.cons_append,List.nil_append] using h

-- Clear k low binary digits without touching the suffix.
def ticks : Nat → Nat
  | 0 => 0
  | k+1 => ticks k + (4*k+8) + ticks k

theorem clear (k : Nat) (R : List Bool) :
    run0 table (ticks k) (K (rep TT k++R)) = some (K (rep FT k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (TT++R)
    have h2 := decr k R
    have h3 := ih (FT++R)
    simp only [List.append_assoc] at h1 h2 h3
    have h := join0 (join0 h1 h2) h3
    simpa only [ticks,rep,List.append_assoc,← List.append_assoc (rep TT k) TT R,rep_snoc TT k,
      ← List.append_assoc (rep FT k) FT R,rep_snoc FT k] using h

theorem turn (n : Nat) :
    run0 table 11 (D n) = some ⟨5,[true]++rep TT n++FF,[false,true,false]⟩ := by rfl

theorem onesCommute (n : Nat) : [true]++rep TT n = rep TT n++[true] := by
  simpa only [List.singleton_append] using rotate true [true] n

theorem toK (n : Nat) : run0 table (16+2*n) (D n) = some (K (rep TT n++FT)) := by
  have h1 := turn n
  rw [onesCommute n] at h1
  simp only [List.append_assoc] at h1
  have h2 := fSweep n [false,true,false]
  have h3 := fFinish (rep TT n++[false,true,false])
  have h := join0 (join0 h1 h2) h3
  rw [show 16+2*n=11+2*n+5 by omega]
  simpa only [K,List.append_assoc,List.cons_append,List.nil_append] using h

theorem overflowAtom (k : Nat) :
    run0 table 2 (B (rep TT k++[true,false,false]) [false]) =
      some ⟨3,[false,false,true]++rep TT k++[true,false,false],[]⟩ := by rfl

theorem overflow (n : Nat) : run0 table (2*n+6) (K (rep FT n++FT)) = some (D (n+1)) := by
  have h1 := pre (rep FT (n+1))
  have h2 := carry (n+1) [true,false,false] [false]
  have h3 := overflowAtom (n+1)
  have h := join0 (join0 h1 h2) h3
  rw [show 2*n+6=2+2*(n+1)+2 by omega]
  have hrep : rep FT (n+1) = rep FT n++FT := by rw [rep_snoc]; rfl
  rw [hrep] at h
  have hL : [false,false,true]++rep TT (n+1)++[true,false,false] =
      FF++TT++rep TT (n+1)++FF := by
    calc
      _ = FF++([true]++(rep TT (n+1)++[true]))++FF := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [← onesCommute (n+1)]; rfl
  rw [hL] at h
  exact h

def family (n : Nat) := D (n+1)
theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) :
    run0 table ((16+2*(n+1))+ticks (n+1)+(2*(n+1)+6)) (family n) =
      some (family (n+1)) := by
  exact join0 (join0 (toK (n+1)) (clear (n+1) FT)) (overflow (n+1))

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 (fun n => (16+2*(n+1))+ticks (n+1)+(2*(n+1)+6)) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent6Raw57RAPumps.M28
