import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120Pumps
open BB6Coverage BB6Coverage.Agent31Pump
namespace M1201
-- 1RB0LE_1RC0LA_0RD1RA_1LD1RE_0RF1LE_---0RB
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
abbrev triple : List Bool := [true,true,true]
abbrev base : List Bool := triple ++ [false]
def P (n : Nat) : List Bool := rep triple n
def atA (L R : List Bool) : Z0 := ⟨0,R.headD false :: L,R.tail⟩
def startA (n : Nat) (R : List Bool) : Z0 := atA base (P n ++ R)
def endA (n : Nat) (R : List Bool) : Z0 := atA (P n ++ base) R
theorem sweep3 (L R : List Bool) : run0 table 3 ⟨4,triple++L,R⟩ = some ⟨4,L,triple++R⟩ := by rfl
theorem sweepN (n : Nat) (R : List Bool) :
    run0 table (3*n) ⟨4,P n++[false],R⟩ = some ⟨4,[false],P n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := sweep3 (P n++[false]) R
    have h2 := ih (triple++R)
    have h := join0 h1 h2
    rw [Nat.mul_succ, Nat.add_comm (3*n) 3]
    simpa only [P,rep,List.append_assoc,← List.append_assoc (rep triple n) triple R,rep_snoc triple n] using h
theorem reset (R : List Bool) : run0 table 6 ⟨4,[false],triple++R⟩ = some (atA base R) := by rfl
theorem resetN (n : Nat) (R : List Bool) :
    run0 table (3*(n+1)+6) ⟨4,P n++base,R⟩ = some (startA n R) := by
  have hs : P n++base = P (n+1)++[false] := by
    simp only [P,rep,List.append_assoc,← List.append_assoc (rep triple n) triple [false],rep_snoc triple n]
  have h := join0 (sweepN (n+1) R) (reset (P n++R))
  rw [hs]
  simpa only [P,rep,List.append_assoc,startA] using h
theorem dec1 (L R : List Bool) : run0 table 1 (atA L (triple++R)) = some ⟨4,L,[false,true,true]++R⟩ := by rfl
theorem dec2 (L R : List Bool) : run0 table 3 (atA L ([false,true,true]++R)) = some ⟨4,L,[false,false,true]++R⟩ := by rfl
theorem carry (L R : List Bool) : run0 table 3 (atA L ([false,false,true]++R)) = some (atA (triple++L) R) := by rfl
def T : Nat → Nat
  | 0 => 0
  | n+1 => T n + 1 + (3*(n+1)+6) + T n + 3 + (3*(n+1)+6) + T n + 3
/-- Ternary countdown with arbitrary untouched higher suffix. -/
theorem count (n : Nat) (R : List Bool) : run0 table (T n) (startA n R) = some (endA n R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (triple++R)
    have h2 := dec1 (P n++base) R
    have h3 := resetN n ([false,true,true]++R)
    have h4 := ih ([false,true,true]++R)
    have h5 := dec2 (P n++base) R
    have h6 := resetN n ([false,false,true]++R)
    have h7 := ih ([false,false,true]++R)
    have h8 := carry (P n++base) R
    have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7) h8
    have hs : startA n (triple++R) = startA (n+1) R := by
      unfold startA
      rw [← List.append_assoc, show P n++triple = P (n+1) by simp only [P,rep_snoc,rep]]
    rw [hs] at H
    simpa only [T,endA,P,rep,List.append_assoc] using H
theorem highDec (L : List Bool) : run0 table 1 (atA L [true]) = some ⟨4,L,[false]⟩ := by rfl
theorem overflow (L : List Bool) : run0 table 6 (atA (true::L) [false]) = some ⟨4,triple++(true::L),[true]⟩ := by rfl
def family (n : Nat) : Z0 := ⟨4,[false],P (n+2)++[true]⟩
theorem entry : run0 table 37 ⟨0,[],[]⟩ = some (family 0) := by rfl
def cost (n : Nat) : Nat := 6 + T (n+1) + 1 + (3*(n+2)+6) + T (n+1) + 6 + 3*(n+3)
theorem overflowN (n : Nat) : run0 table 6 (endA (n+1) [false]) = some ⟨4,P (n+3)++[false],[true]⟩ := by
  have hh : P n ++ base = triple ++ P n ++ [false] := by
    change rep triple n ++ (triple ++ [false]) = (triple ++ rep triple n) ++ [false]
    rw [← List.append_assoc,rep_snoc]
  have h := overflow (true::true::(P n++base))
  have h1 : true::true::true::(P n++base) = P (n+1)++base := by rfl
  have h2 : triple++(true::true::true::(P n++base)) = P (n+3)++[false] := by
    change triple++(triple++(P n++base)) = P (n+3)++[false]
    rw [hh]
    simp only [P,rep,List.append_assoc]
  rw [h2,h1] at h
  exact h
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := reset (P (n+1)++[true])
  have h2 := count (n+1) [true]
  have h3 := highDec (P (n+1)++base)
  have h4 := resetN (n+1) [false]
  have h5 := count (n+1) [false]
  have h6 := overflowN n
  have h7 := sweepN (n+3) [true]
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  simpa only [cost,family,startA,endA,P,rep,List.append_assoc, Nat.add_assoc] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 37 cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms count
#print axioms growth
#print axioms never
end M1201
end BB6.Agent3Raw120Pumps
