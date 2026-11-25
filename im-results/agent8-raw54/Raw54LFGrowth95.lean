import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth95
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def P : List Bool := [true,false,false]
def Q : List Bool := [false,false,true]
def U : List Bool := [true,false,true]
def V : List Bool := [true,true,false]
def W : List Bool := [false,true,true]
def cfg (n : Nat) : Z0 := ⟨5,[],true::(rep Q (n+1) ++ [true])⟩
def mid (n : Nat) : Z0 := ⟨5,[true],true::(rep Q (n+1) ++ [false])⟩

theorem rotP (n : Nat) (R : List Bool) : true::(rep Q n ++ R) = rep P n ++ true::R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc]; change true::false::false::true::(rep Q n ++ R) = true::false::false::(rep P n ++ true::R); rw [ih]
theorem rotU (n : Nat) : true::rep U n = rep V n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc]; change true::true::false::true::rep U n = true::true::false::(rep V n ++ [true]); rw [ih]
theorem rotW (n : Nat) : [true,true] ++ rep W n = rep V n ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc]; change true::true::false::([true,true] ++ rep W n) = true::true::false::(rep V n ++ [true,true]); rw [ih]

theorem pairRep (P : List Bool) (n : Nat) : rep (P++P) n = rep P (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+2 by omega]; simp only [rep,ih,List.append_assoc]

theorem phase1 (n : Nat) : ∃ t,0<t ∧ run0 table t (cfg (2*n)) = some (mid (2*n)) := by
  have a : run0 table 1 (cfg (2*n)) = some ⟨2,[true,true],rep Q (2*n+1) ++ [true]⟩ := by rfl
  have b := sweepR table 2 [true,true] [] Q U 3 (by intro L R; rfl) (2*n+1) [] [true]
  have c : run0 table 6 ⟨2,[true,true] ++ rep U (2*n+1),[true]⟩ = some ⟨5,true::rep U (2*n),[true,false,false,true,false]⟩ := by rfl
  rw [rotU] at c
  have d := sweepL table 5 [] [] (V++V) (P++P) 6 (by intro L R; rfl) n [true] [true,false,false,true,false]
  rw [pairRep,pairRep] at d
  simp only [List.nil_append,List.append_nil] at b d
  have H := join0 (join0 (join0 a b) c) d
  refine ⟨1+3*(2*n+1)+6+6*n,by omega,?_⟩
  unfold mid
  rw [rotP]
  have h : rep P (2*n) ++ [true,false,false,true,false] = rep P (2*n+1) ++ [true,false] := by
    change rep P (2*n) ++ (P ++ [true,false]) = (P ++ rep P (2*n)) ++ [true,false]
    rw [← List.append_assoc,rep_snoc]
  rw [h] at H
  exact H

theorem phase2 (n : Nat) : ∃ t,0<t ∧ run0 table t (mid (2*n)) = some (cfg (2*(n+1))) := by
  have a : run0 table 3 (mid (2*n)) = some ⟨2,[true,true,true],rep Q (2*n+1) ++ [false]⟩ := by rfl
  have b := sweepR table 2 [true,true,true] [] Q W 3 (by intro L R; rfl) (2*n+1) [] [false]
  have c : run0 table 9 ⟨2,[true,true,true] ++ rep W (2*n+1),[false]⟩ = some ⟨5,[true,true] ++ rep W (2*n+1),[true,false,false,true,true]⟩ := by rfl
  rw [rotW] at c
  have d := sweepL table 5 [] [] (V++V) (P++P) 6 (by intro L R; rfl) n [true,true,false,true,true] [true,false,false,true,true]
  rw [pairRep,pairRep] at d
  have c' : run0 table 9 ⟨2,[true,true,true] ++ rep W (2*n+1),[false]⟩ = some ⟨5,rep V (2*n) ++ [true,true,false,true,true],[true,false,false,true,true]⟩ := by
    have h : rep V (2*n+1) ++ [true,true] = rep V (2*n) ++ [true,true,false,true,true] := by
      change (V ++ rep V (2*n)) ++ [true,true] = rep V (2*n) ++ (V ++ [true,true])
      rw [← rep_snoc V (2*n),List.append_assoc]
    rw [h] at c
    exact c
  have e : run0 table 6 ⟨5,[true,true,false,true,true],rep P (2*n) ++ [true,false,false,true,true]⟩ = some ⟨5,[],P ++ P ++ (rep P (2*n) ++ [true,false,false,true,true])⟩ := by rfl
  simp only [List.nil_append,List.append_nil] at b d
  have H := join0 (join0 (join0 (join0 a b) c') d) e
  refine ⟨3+3*(2*n+1)+9+6*n+6,by omega,?_⟩
  unfold cfg
  rw [rotP,show 2*(n+1)+1=2*n+3 by omega]
  have h : P ++ P ++ (rep P (2*n) ++ [true,false,false,true,true]) = rep P (2*n+3) ++ [true,true] := by
    change P ++ (P ++ (rep P (2*n) ++ (P ++ [true,true]))) = rep P (2*n+3) ++ [true,true]
    rw [← List.append_assoc (rep P (2*n)) P,rep_snoc]
    simp only [rep,List.append_assoc]
  rw [h] at H
  exact H

def family (n : Nat) : Z0 := cfg (2*n)
theorem first : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,h⟩ := phase1 n
  obtain ⟨u,hu,g⟩ := phase2 n
  exact ⟨t+u,by omega,join0 h g⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 8 first next m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth95
