import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw112Alternating
open BB6Coverage BB6Coverage.Agent31Pump

-- Leaf 2124: 1RB0LF_1RC0RA_0RD0LE_1LD1RE_1LA1LC_1LE---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [false,true,false,true]
abbrev B (L R : List Bool) : Z0 := ⟨1,true::true::L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev D (n : Nat) : Z0 := ⟨3,[false,false,true,true] ++ rep P n,[]⟩
def X (a b : Nat) : Z0 := E [false] (rep P (2*a+1) ++ [false] ++ rep P b ++ [true,true])

theorem rep_add (p : List Bool) (a b : Nat) : rep p (a+b)=rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem rep_end (n : Nat) : rep P (n+1) = rep P n ++ P := (rep_snoc P n).symm

theorem qpow (n : Nat) : rep Q n = rep P (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Q ++ rep Q n = rep P (2*(n+1))
    rw [ih,show 2*(n+1)=2*n+2 by omega]
    rfl

theorem bOne (L R : List Bool) : run0 table 2 (B L (P++R)) = some (B (P++L) R) := by rfl

theorem bSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (B L (rep P n++R)) = some (B (rep P n++L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have g := join0 (bOne L (rep P n++R)) (ih (P++L))
    rw [show 2+2*n=2*(n+1) by omega] at g
    have eq : rep P n ++ (P++L) = P++rep P n++L := by rw [←List.append_assoc,rep_snoc]
    rw [eq] at g
    simpa only [rep,List.append_assoc] using g

theorem eOne (L R : List Bool) : run0 table 8 (E (Q++false::L) R) = some (E (false::L) (Q++R)) := by rfl

theorem eLast (R : List Bool) : run0 table 8 (E Q R) = some (E [false] (Q++R)) := by rfl

theorem eOdd (n : Nat) (R : List Bool) :
    run0 table (8*n) (E (rep Q n++P) R) = some (E P (rep Q n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 8 (E (rep Q (n+1)++P) R) = some (E (rep Q n++P) (Q++R)) := by
      cases n <;> rfl
    have g := join0 h (ih (Q++R))
    rw [show 8+8*n=8*(n+1) by omega,←List.append_assoc,rep_snoc] at g
    exact g

theorem eEven (n : Nat) (R : List Bool) :
    run0 table (8*(n+1)) (E (rep Q (n+1)) R) = some (E [false] (rep Q (n+1)++R)) := by
  induction n generalizing R with
  | zero => exact eLast R
  | succ n ih =>
    have h : run0 table 8 (E (rep Q (n+1+1)) R) = some (E (rep Q (n+1)) (Q++R)) := by rfl
    have g := join0 h (ih (Q++R))
    rw [show 8+8*(n+1)=8*(n+1+1) by omega,←List.append_assoc,rep_snoc] at g
    exact g

theorem xStart (n : Nat) : run0 table (8*n+29) (D (2*n+2)) = some (X 0 (2*n+3)) := by
  have h1 : run0 table 8 (D (2*n+2)) = some (E (rep P (2*n+3)) [true,true]) := by
    rfl
  have h2 := eOdd (n+1) [true,true]
  rw [qpow] at h2
  have e : rep P (2*(n+1)) ++ P = rep P (2*(n+1)+1) := by rw [rep_add]; rfl
  rw [e] at h2
  have eq : 2*(n+1)+1=2*n+3 := by omega
  rw [eq] at h2
  have h3 : run0 table 13 (E P (rep P (2*(n+1))++[true,true])) = some (X 0 (2*n+3)) := by
    rfl
  have g := join0 (join0 h1 h2) h3
  rw [show 8+8*(n+1)+13=8*n+29 by omega] at g
  exact g

theorem xStep (a b : Nat) : run0 table (12*a+18) (X a (b+1)) = some (X (a+1) b) := by
  let R := rep P b ++ [true,true]
  let k := 2*a+1
  have h1 : run0 table 2 (X a (b+1)) = some (B [] (rep P k ++ (false::(P++R)))) := by
    unfold X k R
    simp only [rep,List.append_assoc,List.cons_append,List.nil_append]
    rfl
  have h2 := bSweep k [] (false::(P++R))
  simp only [List.append_nil] at h2
  have h3 : run0 table 6 (B (rep P k) (false::(P++R))) = some (E (rep P (k+1)) (P++false::R)) := by
    rfl
  have h4 := eEven a (P++false::R)
  rw [qpow,show 2*(a+1)=k+1 by omega] at h4
  have g := join0 (join0 (join0 h1 h2) h3) h4
  have er : rep P (k+1) ++ (P++false::R) = rep P (2*(a+1)+1) ++ false::R := by
    rw [←List.append_assoc,←rep_end,show k+1+1=2*(a+1)+1 by omega]
  rw [er] at g
  have et : 2+2*k+6+8*(a+1)=12*a+18 := by dsimp [k]; omega
  rw [et] at g
  simpa only [X,R,List.append_assoc,List.cons_append,List.nil_append] using g

def Reach (x y : Z0) : Prop := ∃ t : Nat, run0 table t x = some y

theorem reachJoin {x y z : Z0} (h : Reach x y) (g : Reach y z) : Reach x z := by
  obtain ⟨t,h⟩ := h; obtain ⟨u,g⟩ := g
  exact ⟨t+u,join0 h g⟩

theorem xIter (a b : Nat) : Reach (X a b) (X (a+b) 0) := by
  induction b generalizing a with
  | zero => exact ⟨0,rfl⟩
  | succ b ih =>
    have g := reachJoin ⟨_,xStep a b⟩ (ih (a+1))
    rw [show a+1+b=a+(b+1) by omega] at g
    exact g

theorem xFinish (a : Nat) : Reach (X a 0) (D (2*a+4)) := by
  let k := 2*a+2
  have e0 : X a 0 = E [false] (rep P k ++ [true]) := by
    change E [false] (rep P (2*a+1) ++ [false] ++ [] ++ [true,true]) = E [false] (rep P ((2*a+1)+1) ++ [true])
    have he := congrArg (fun w => E [false] (w ++ [true])) (rep_end (2*a+1))
    simpa only [P,List.append_assoc,List.cons_append,List.nil_append] using he.symm
  have h1 : run0 table 2 (X a 0) = some (B [] (rep P k ++ [true])) := by rw [e0]; rfl
  have h2 := bSweep k [] [true]
  simp only [List.append_nil] at h2
  have h3 : run0 table 8 (B (rep P k) [true]) = some (E (rep P k) [false,true,false]) := by rfl
  have h4 := eEven a [false,true,false]
  rw [qpow,show 2*(a+1)=k by omega] at h4
  have g := join0 (join0 (join0 h1 h2) h3) h4
  have e1 : rep P k ++ [false,true,false] = rep P (k+1) ++ [false] := by
    have he := congrArg (fun w => w ++ [false]) (rep_end k)
    simpa only [P,List.append_assoc,List.cons_append,List.nil_append] using he.symm
  rw [e1] at g
  have h5 : run0 table 2 (E [false] (rep P (k+1) ++ [false])) = some (B [] (rep P (k+1) ++ [false])) := by rfl
  have h6 := bSweep (k+1) [] [false]
  simp only [List.append_nil] at h6
  have h7 : run0 table 4 (B (rep P (k+1)) [false]) = some (D (k+2)) := by rfl
  have H := join0 (join0 (join0 g h5) h6) h7
  rw [show k+2=2*a+4 by omega] at H
  exact ⟨_,H⟩

def family (n : Nat) : Z0 := D (12*2^n-6)
theorem entry : run0 table 92 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : ∃ t : Nat, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide)
  let k := 6*2^n-4
  have e1 : 2*k+2=12*2^n-6 := by dsimp [k]; omega
  have e2 : 2*(2*k+3)+4=12*2^(n+1)-6 := by dsimp [k]; rw [Nat.pow_succ]; omega
  have g := reachJoin (xIter 0 (2*k+3)) (by simpa only [Nat.zero_add] using xFinish (2*k+3))
  obtain ⟨u,g⟩ := g
  have h := join0 (xStart k) g
  rw [e1,e2] at h
  exact ⟨_,by omega,h⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth n)
theorem cost_pos (n : Nat) : 0<cost n := (Classical.choose_spec (growth n)).1
theorem cost_run (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (Classical.choose_spec (growth n)).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 92 cost entry cost_pos cost_run m hm

#print axioms growth
#print axioms never
end BB6.Agent8Raw112Alternating
