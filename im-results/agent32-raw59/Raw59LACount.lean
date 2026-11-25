import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59LACount
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def rpt (p : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => p ++ rpt p n

theorem rpt_snoc (p : List Bool) (n : Nat) : rpt p n ++ p = p ++ rpt p n := by
  induction n with
  | zero => simp [rpt]
  | succ n ih => simp only [rpt,List.append_assoc,ih]

abbrev Z (n : Nat) := rpt [false,false] n
abbrev O (n : Nat) := rpt [true,true] n
abbrev marker : List Bool := [false,true,true,true,true]
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def C (L R : List Bool) : Z0 := ⟨2,L,R⟩

-- C scanning right: change each pair of ones to zeros, with the scanned 1 as frame.
theorem scan (k : Nat) (L R : List Bool) :
    run0 table (2*k) (C (true::L) (O k ++ R)) = some (C (true::(Z k ++ L)) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 2 (C (true::L) ([true,true]++O k++R)) =
        some (C (true::false::false::L) (O k++R)) := by rfl
    have h2 := ih (false::false::L)
    have H := join0 h1 h2
    rw [show 2+2*k=2*(k+1) by omega] at H
    have he : Z k ++ false::false::L = Z (k+1) ++ L := by
      change Z k ++ ([false,false] ++ L) = _
      rw [← List.append_assoc,rpt_snoc]
      rfl
    rw [he] at H
    exact H

-- A carry consumes a binary one, pushing two ones on the right.
theorem carry (L R : List Bool) :
    run0 table 2 (B (true::false::L) R) = some (B L (true::true::R)) := by rfl

theorem zero_comm (k : Nat) (L : List Bool) : Z k ++ false::L = false::(Z k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false::false::(Z k ++ false::L) = false::false::false::(Z k ++ L)
    rw [ih]

theorem turn (L R : List Bool) : run0 table 8 (C (true::false::L) (marker++R)) = some (B (false::false::L) (marker++R)) := by rfl

-- Clearing a zero digit after the carry restores the lower digits as zeros.
theorem reset (k : Nat) (L R : List Bool) :
    run0 table (8+2*k) (B (false::false::L) (O k ++ marker ++ R)) =
      some (B (Z k ++ true::false::L) (marker ++ R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (B (false::false::L) (O (k+1) ++ marker ++ R)) =
        some (C (true::true::false::L) (true::O k ++ marker ++ R)) := by rfl
    have h2 : run0 table 1 (C (true::true::false::L) (true::O k ++ marker ++ R)) =
        some (C (true::false::true::false::L) (O k ++ marker ++ R)) := by rfl
    have h3 := scan k (false::true::false::L) (marker++R)
    have h4 : run0 table 8 (C (true::(Z k ++ false::true::false::L)) (marker++R)) =
        some (B (false::false::Z k ++ true::false::L) (marker++R)) := by
      rw [zero_comm]
      exact turn (Z k ++ true::false::L) R
    rw [← List.append_assoc] at h3
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show 1+1+2*k+8=8+2*(k+1) by omega] at H
    exact H

def cost : Nat → Nat
  | 0 => 0
  | k+1 => cost k + (8+2*k) + cost k + 2

theorem count (k : Nat) (L R : List Bool) :
    run0 table (cost k) (B (Z k ++ L) (marker++R)) = some (B L (O k ++ marker++R)) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (false::false::L)
    have h2 := reset k L R
    have h3 := ih (true::false::L)
    have h4 := carry L (O k ++ marker++R)
    have he : Z k ++ false::false::L = Z (k+1) ++ L := by
      change Z k ++ ([false,false] ++ L) = _
      rw [← List.append_assoc,rpt_snoc]
      rfl
    rw [he] at h1
    exact join0 (join0 (join0 h1 h2) h3) h4

theorem sentinel (R : List Bool) : run0 table 2 (B [true] R) = some (B [] (true::true::R)) := by rfl

def family (n : Nat) : Z0 := B [] (O n ++ marker)

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem prepare (k : Nat) : run0 table (8+2*k) (family k) = some (B (Z k ++ [true]) marker) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (family (k+1)) = some (C [true,true] (true::O k ++ marker)) := by rfl
    have h2 : run0 table 1 (C [true,true] (true::O k ++ marker)) = some (C [true,false,true] (O k ++ marker)) := by rfl
    have h3 := scan k [false,true] marker
    have h4 : run0 table 8 (C (true::(Z k ++ [false,true])) marker) = some (B (false::false::Z k ++ [true]) marker) := by
      change run0 table 8 (C (true::(Z k ++ false::[true])) marker) = _
      rw [zero_comm]
      exact turn (Z k ++ [true]) []
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show 1+1+2*k+8=8+2*(k+1) by omega] at H
    exact H

def epoch (n : Nat) := 8+2*n+cost n+2

theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
  have h1 := prepare n
  have h2 := count n [true] []
  simp only [List.append_nil] at h2
  have h3 := sentinel (O n ++ marker)
  exact join0 (join0 h1 h2) h3

theorem cost_exact (n : Nat) : cost n + 2*n+12 = 12*2^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cost,Nat.pow_succ]; omega

theorem epoch_exact (n : Nat) : epoch n + 2 = 12*2^n := by
  have h := cost_exact n
  unfold epoch
  omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 epoch entry (by intro n; unfold epoch; omega) growth m hm

#print axioms count
#print axioms epoch_exact
#print axioms never
end BB6.Agent32Raw59LACount
