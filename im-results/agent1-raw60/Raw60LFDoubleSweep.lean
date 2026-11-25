import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LFDoubleSweep
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev U (n : Nat) := List.replicate n true

def B : Nat → List Bool
  | 0 => []
  | n+1 => false::true::true::B n

def C : Nat → List Bool
  | 0 => []
  | n+1 => true::false::true::C n

theorem Bsnoc (n : Nat) : B n ++ [false,true,true] = B (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [B,List.cons_append,ih]

theorem Brotate (n : Nat) (R : List Bool) :
    true::(B n++false::true::R) = C (n+1)++R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [B,C,List.cons_append]; rw [ih]; rfl

theorem scanL (n : Nat) (L R : List Bool) :
    run0 table (3*n) (A (U (3*n)++L) R) = some (A L (B n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 3 (A (U (3*(n+1))++L) R) = some (A (U (3*n)++L) (false::true::true::R)) := by
      rw [show 3*(n+1)=3*n+1+1+1 by omega]; rfl
    have H := join0 h1 (ih (false::true::true::R))
    change run0 table (3+3*n) (A (U (3*(n+1))++L) R) = some (A L (B n++([false,true,true]++R))) at H
    rw [show 3+3*n=3*(n+1) by omega,← List.append_assoc,Bsnoc] at H
    exact H

theorem scanR (n k : Nat) (L R : List Bool) :
    run0 table (7*n) (A (false::(U (k+2)++L)) (C n++R)) =
      some (A (false::(U (k+2+3*n)++L)) R) := by
  induction n generalizing k with
  | zero => simp [C,run0]
  | succ n ih =>
    have h1 : run0 table 7 (A (false::(U (k+2)++L)) (C (n+1)++R)) =
      some (A (false::(U (k+3+2)++L)) (C n++R)) := by
      rw [show k+3+2=k+1+1+1+1+1 by omega]; rfl
    have H := join0 h1 (ih (k+3))
    rw [show 7+7*n=7*(n+1) by omega,show k+3+2+3*n=k+2+3*(n+1) by omega] at H
    exact H

theorem head (k : Nat) (L : List Bool) :
    run0 table 4 (D (false::false::(U (k+1)++L)) []) = some (A (U (k+3)++L) []) := by
  rw [show k+3=k+1+1+1 by omega]; rfl

theorem startScan (k : Nat) (L R : List Bool) :
    run0 table 3 (A (false::(U k++L)) (false::true::true::R)) =
      some (A (U (k+2)++L) (false::true::R)) := by rfl

theorem firstTurn (L R : List Bool) :
    run0 table 3 (A (true::true::false::L) R) = some (D (true::false::L) (true::R)) := by rfl

theorem initialTurn (n : Nat) (L R : List Bool) :
    run0 table 10 (D (true::false::L) (true::(B (n+1)++false::true::R))) =
      some (A (false::true::true::false::true::true::true::false::L) (C n++R)) := by
  rw [Brotate]; rfl

theorem otherTurn (n : Nat) (L R : List Bool) :
    run0 table 11 (A (true::false::L) (B (n+1)++false::true::R)) =
      some (A (false::true::true::false::true::true::true::L) (C n++R)) := by
  change run0 table 11 (A (true::false::L) (false::true::true::(B n++false::true::R))) = _
  rw [Brotate]; rfl

def stage (b j : Nat) (R : List Bool) : Z0 := A (false::(U (3*b+2)++false::(U (3*j)++[false,true,true,true]))) R

theorem advance (b j a : Nat) :
    run0 table (3+3*(b+1)+11+7*b) (stage b j (B (a+1))) = some (stage b (j+1) (B a)) := by
  let L := U (3*j)++[false,true,true,true]
  have h1 := startScan (3*b+2) (false::L) (B a)
  have h2 := scanL (b+1) (true::false::L) (false::true::B a)
  have he : U (3*b+2+2)++false::L = U (3*(b+1))++true::false::L := by
    change List.replicate (3*b+2+2) true++false::L = List.replicate (3*(b+1)) true++true::false::L
    rw [show 3*b+2+2=3*(b+1)+1 by omega,List.replicate_succ',List.append_assoc]; rfl
  rw [he] at h1
  have h3 := otherTurn b L (B a)
  have h4 := scanR b 0 (false::true::true::true::L) (B a)
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have hu : true::true::true::L = U (3*(j+1))++[false,true,true,true] := by
    dsimp [L]; rw [show 3*(j+1)=3*j+1+1+1 by omega]; rfl
  rw [hu] at H
  unfold stage
  rw [show 0+2+3*b=3*b+2 by omega] at H
  exact H

theorem loop (a b j : Nat) :
    run0 table ((3+3*(b+1)+11+7*b)*a) (stage b j (B a)) = some (stage b (j+a) []) := by
  induction a generalizing j with
  | zero => simp [B,run0]
  | succ a ih =>
    have H := join0 (advance b j a) (ih (j+1))
    rw [show (3+3*(b+1)+11+7*b)+(3+3*(b+1)+11+7*b)*a=(3+3*(b+1)+11+7*b)*(a+1) by simp only [Nat.mul_succ]; exact Nat.add_comm _ _,show j+1+a=j+(a+1) by omega] at H
    exact H

def family (a b : Nat) : Z0 := D (false::false::(U (3*a+1)++false::(U (3*(b+1))++[false,true,true,true]))) []
def cost (a b : Nat) := 4+3*(a+1)+3+3*(b+1)+3+10+7*b+(3+3*(b+1)+11+7*b)*a+3

theorem growth (a b : Nat) :
    run0 table (cost a b) (family a b) = some (family (b+1) a) := by
  let L := U (3*(b+1))++[false,true,true,true]
  have h1 := head (3*a) (false::L)
  rw [show 3*a+3=3*(a+1) by omega] at h1
  have h2 := scanL (a+1) (false::L) []
  simp only [List.append_nil] at h2
  have h3 := startScan (3*(b+1)) [false,true,true,true] (B a)
  have h4 := scanL (b+1) [true,true,false,true,true,true] (false::true::B a)
  have hu : U (3*(b+1)+2)++[false,true,true,true] = U (3*(b+1))++[true,true,false,true,true,true] := by
    change List.replicate (3*(b+1)+2) true++[false,true,true,true] = List.replicate (3*(b+1)) true++[true,true,false,true,true,true]
    rw [← List.replicate_append_replicate,List.append_assoc]; rfl
  rw [hu] at h3
  have h5 := firstTurn [true,true,true] (B (b+1)++false::true::B a)
  have h6 := initialTurn b [true,true,true] (B a)
  have h7 := scanR b 0 [false,true,true,true,false,true,true,true] (B a)
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  have hs : A (false::(U (0+2+3*b)++[false,true,true,true,false,true,true,true])) (B a) = stage b 1 (B a) := by
    unfold stage; rw [show 0+2+3*b=3*b+2 by omega]; rfl
  rw [hs] at H
  have h8 := loop a b 1
  have h9 : run0 table 3 (stage b (1+a) []) = some (family (b+1) a) := by
    unfold stage family
    rw [show 3*(1+a)=3*(a+1) by omega,show 3*(b+1)+1=3*b+2+1+1 by omega]
    rfl
  exact join0 (join0 H h8) h9

def pair (n : Nat) : Nat × Nat := match n with | 0 => (0,0) | n+1 => ((pair n).2+1,(pair n).1)
theorem entry : run0 table 37 ⟨0,[],[]⟩ = some (family 0 0) := by rfl
theorem positive (a b : Nat) : 0 < cost a b := by unfold cost; omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => family (pair n).1 (pair n).2) 37 (fun n => cost (pair n).1 (pair n).2) entry (fun n => positive _ _) (fun n => growth _ _) m hm
#print axioms never
#print axioms growth
end BB6.Agent1Raw60LFDoubleSweep
