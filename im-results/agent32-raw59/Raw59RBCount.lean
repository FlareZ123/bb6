import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59RB
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
abbrev Z (k : Nat) := rep [false,false,false] k
abbrev O (k : Nat) := rep [true,true,true] k

def B (k : Nat) (L R : List Bool) : Z0 := ⟨1,R.headD false::(Z k ++ true::L),R.tail⟩
def D (L R : List Bool) : Z0 := ⟨3,L,R⟩

theorem dSweep (k : Nat) (L R : List Bool) :
    run0 table (3*k) (D (Z k ++ L) R) = some (D L (O k ++ R)) := by
  simpa only [List.nil_append,D] using sweepL table 3 [] [] [false,false,false] [true,true,true] 3 (by intro L R; rfl) k L R

theorem dLeave (L R : List Bool) (h : R.headD false=true) :
    run0 table 3 (D (true::L) R) = some (B 0 L R) := by
  cases R with
  | nil => contradiction
  | cons b R =>
    have hb : b=true := h
    subst b
    rfl

theorem reset (k : Nat) (L R : List Bool) :
    run0 table (3*k+6) (B k L ([true,true,true]++R)) = some (B 0 L (O k ++ [true,false,true]++R)) := by
  have h1 : run0 table 3 (B k L ([true,true,true]++R)) = some (D (Z k ++ true::L) ([true,false,true]++R)) := by rfl
  have h2 := dSweep k (true::L) ([true,false,true]++R)
  have hh : (O k ++ [true,false,true]++R).headD false=true := by
    cases k <;> rfl
  have h3 := dLeave L (O k ++ [true,false,true]++R) hh
  rw [List.append_assoc] at h3
  have h := join0 (join0 h1 h2) h3
  rw [show 3+3*k+3=3*k+6 by omega, ← List.append_assoc] at h
  exact h

theorem clear (k : Nat) (L R : List Bool) :
    run0 table 3 (B k L ([true,false,true]++R)) = some (B (k+1) L R) := by rfl

def cost : Nat → Nat
  | 0 => 0
  | k+1 => cost k + (3*k+6) + cost k + 3

theorem count (k : Nat) (L R : List Bool) :
    run0 table (cost k) (B 0 L (O k ++ R)) = some (B k L R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := ih ([true,true,true]++R)
    have h2 := reset k L R
    have h3 := ih ([true,false,true]++R)
    rw [List.append_assoc] at h2
    have h4 := clear k L R
    have h := join0 (join0 (join0 h1 h2) h3) h4
    rw [← List.append_assoc, rep_snoc] at h
    exact h

def family (n : Nat) : Z0 := D (false::(Z (n+1) ++ [true,true])) []

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

def epoch (n : Nat) := 1+3*(n+1)+3+cost (n+1)+3

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  have h1 : run0 table 1 (family n) = some (D (Z (n+1) ++ [true,true]) [true]) := by rfl
  have h2 := dSweep (n+1) [true,true] [true]
  have h3 := dLeave [true] (O (n+1) ++ [true]) (by rfl)
  have h4 := count (n+1) [true] [true]
  have h5 : run0 table 3 (B (n+1) [true] [true]) = some (family (n+1)) := by rfl
  exact join0 (join0 (join0 (join0 h1 h2) h3) h4) h5

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 epoch entry (by intro n; unfold epoch; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent32Raw59RB
