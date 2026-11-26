import Raw54BinaryShape
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.ZeroRB.M51
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.DigitSection BB6.Agent8Raw54.BinaryShape

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def p : List Bool := [true,false]
def u : List Bool := [true,true]
def v : List Bool := [false,false]
def z : List Bool := [false,false,false,false]
def mark : List Bool := [false,true,true]

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,ih,rep];simp only [List.append_assoc]

theorem rep_double (P : List Bool) (n : Nat) : rep P (2*n) = rep (P++P) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2+2*n by omega,rep_add,ih,rep]; simp only [rep,List.append_nil,List.append_assoc]

theorem entry (L R : List Bool) :
    run0 table 6 ⟨4,false::L,mark ++ u ++ R⟩ = some ⟨0,false::(p++L),p ++ [true] ++ R⟩ := by rfl

theorem stop0 (L R : List Bool) :
    run0 table 18 ⟨4,false::L,mark ++ z ++ R⟩ = some ⟨4,false::(p++L),mark ++ u ++ R⟩ := by rfl

theorem over0 (L : List Bool) :
    run0 table 28 ⟨4,false::L,mark ++ u⟩ = some ⟨4,false::L,mark ++ z ++ u⟩ := by rfl

theorem rightOnes (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨0,false::L,rep p n ++ R⟩ = some ⟨0,false::(rep u n ++ L),R⟩ := by
  simpa only [List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [] p u 2 (by intro L R; rfl) n L R

theorem leftOnes (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨0,rep u n ++ L,R⟩ = some ⟨0,L,rep p n ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil] using sweepL table 0 [] [] u p 2 (by intro L R; rfl) n L R

theorem onesSnoc (n : Nat) (L : List Bool) : rep u n ++ true::false::L = true::(rep u n ++ false::L) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,u,List.cons_append,List.nil_append] at *; rw [ih]

theorem loop (n : Nat) (L R : List Bool) :
    run0 table (4*n+6) ⟨0,false::(p++L),rep p n ++ u ++ R⟩ =
      some ⟨0,false::L,rep p (n+2) ++ R⟩ := by
  have h := rightOnes n (p++L) (u++R)
  have h2 : run0 table 2 ⟨0,false::(rep u n ++ p ++ L),u++R⟩ =
      some ⟨0,rep u (n+2) ++ false::L,R⟩ := by
    rw [show rep u n ++ p ++ L = true::(rep u n ++ false::L) by simpa only [p,List.append_assoc,List.cons_append,List.nil_append] using onesSnoc n L]
    simp only [rep,u,List.cons_append,List.nil_append,List.append_assoc]
    rfl
  have H := join0 (by simpa only [List.append_assoc] using h) h2
  have H' := join0 H (leftOnes (n+2) (false::L) R)
  rw [show 2*n+2+2*(n+2)=4*n+6 by omega] at H'
  simpa only [List.append_assoc] using H'

theorem zerosSnoc (n : Nat) (R : List Bool) : rep v n ++ false::R = false::(rep v n ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,v,List.cons_append,List.nil_append] at *; rw [ih]

theorem finish (n : Nat) (L R S : List Bool) (valid : S = z++R ∨ (S=[] ∧ R=[])) :
    run0 table (4*n+18) ⟨0,false::(p++L),rep p n ++ [true] ++ S⟩ =
      some ⟨4,false::L,mark ++ rep v (n+1) ++ u ++ R⟩ := by
  have h := rightOnes n (p++L) ([true]++S)
  have h2 : run0 table 8 ⟨0,false::(rep u n ++ p ++ L),[true]++S⟩ =
      some ⟨4,rep u (n+2) ++ false::L,mark++R⟩ := by
    rw [show rep u n ++ p ++ L = true::(rep u n ++ false::L) by simpa only [p,List.append_assoc,List.cons_append,List.nil_append] using onesSnoc n L]
    simp only [rep,u,List.cons_append,List.nil_append]
    rcases valid with rfl | ⟨rfl,rfl⟩ <;> rfl
  have H := join0 (by simpa only [List.append_assoc] using h) h2
  have h3 := sweepL table 4 [] [] u v 2 (by intro L R; rfl) (n+2) (false::L) (mark++R)
  have H' := join0 H (by simpa only [List.nil_append,List.append_nil] using h3)
  have eq : rep v (n+2) ++ (mark++R) = [false,false,false] ++ (rep v (n+1) ++ u ++ R) := by
    simp only [rep,v,mark,u,List.cons_append,List.nil_append,List.append_assoc]
    have hs := zerosSnoc (n+1) ([true,true]++R)
    simp only [v,rep,List.cons_append,List.nil_append,List.append_assoc] at hs
    rw [hs]
  rw [eq] at H'
  have h4 (T : List Bool) : run0 table 6 ⟨4,false::L,[false,false,false]++T⟩ = some ⟨4,false::L,mark++T⟩ := by rfl
  have H'' := join0 H' (h4 (rep v (n+1) ++ u ++ R))
  rw [show 2*n+8+2*(n+2)+6=4*n+18 by omega] at H''
  simpa only [List.append_assoc] using H''

def loopCost (k : Nat) : Nat → Nat
  | 0 => 4*k+18
  | n+1 => 4*k+6+loopCost (k+2) n

theorem loopMany (k n : Nat) (L R S : List Bool) (valid : S=z++R ∨ (S=[] ∧ R=[])) :
    run0 table (loopCost k n) ⟨0,false::(rep p (n+1) ++ L),rep p k ++ rep u n ++ [true] ++ S⟩ =
    some ⟨4,false::L,mark ++ rep v (k+2*n+1) ++ u ++ R⟩ := by
  induction n generalizing k with
  | zero =>
    simpa only [loopCost,rep,Nat.mul_zero,Nat.add_zero,List.nil_append,List.append_nil,List.append_assoc] using finish k L R S valid
  | succ n ih =>
    have h := loop k (rep p (n+1) ++ L) (rep u n ++ [true] ++ S)
    have h' := ih (k+2)
    have H := join0 h (by simpa only [List.append_assoc] using h')
    rw [show k+2+2*n+1=k+2*(n+1)+1 by omega] at H
    simpa only [loopCost,rep,List.append_assoc] using H

theorem onesComm (n : Nat) (R : List Bool) : rep u n ++ true::R = true::(rep u n ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,u,List.cons_append,List.nil_append] at *; rw [ih]

theorem stopSucc (n : Nat) (L R : List Bool) :
    run0 table (6+loopCost 1 n) ⟨4,false::(rep p (n+1)++L),mark++rep u (n+1)++z++R⟩ =
      some ⟨4,false::(p++L),mark++rep z (n+1)++u++R⟩ := by
  have h := entry (rep p (n+1)++L) (rep u n++z++R)
  have h2 := loopMany 1 n (p++L) R (z++R) (Or.inl rfl)
  have eqL : p ++ (rep p (n+1) ++ L) = rep p (n+1) ++ (p++L) := by
    simp only [← List.append_assoc,rep_snoc p (n+1)]
  have eqR : p ++ [true] ++ (rep u n ++ z ++ R) = rep p 1 ++ rep u n ++ [true] ++ (z++R) := by
    simp only [rep,List.append_assoc,List.append_nil,List.cons_append,List.nil_append,onesComm]
  have h' : run0 table 6 ⟨4,false::(rep p (n+1)++L),mark++rep u (n+1)++z++R⟩ =
      some ⟨0,false::(rep p (n+1)++(p++L)),rep p 1 ++ rep u n ++ [true] ++ (z++R)⟩ := by
    rw [← eqL,← eqR]
    simpa only [rep,List.append_assoc] using h
  have H := join0 h' h2
  rw [show 1+2*n+1=2*(n+1) by omega,rep_double] at H
  simpa only [show v++v=z by rfl] using H

theorem overflow (n : Nat) (L : List Bool) :
    run0 table (6+loopCost 1 n) ⟨4,false::(rep p n++L),mark++rep u n++u⟩ =
      some ⟨4,false::L,mark++rep z (n+1)++u⟩ := by
  have h := entry (rep p n++L) (rep u n)
  have h2 := loopMany 1 n L [] [] (Or.inr ⟨rfl,rfl⟩)
  have h' : run0 table 6 ⟨4,false::(rep p n++L),mark++rep u n++u⟩ =
    some ⟨0,false::(rep p (n+1)++L),rep p 1 ++ rep u n ++ [true] ++ []⟩ := by
    simpa only [rep,List.append_assoc,List.append_nil,rep_snoc,onesComm,List.cons_append,List.nil_append] using h
  have H := join0 h' h2
  rw [show 1+2*n+1=2*(n+1) by omega,rep_double] at H
  simpa only [List.append_nil,show v++v=z by rfl] using H

def base : List Bool := [true,false,true,false,true,false]
def sec (xs : List Bool) : Z0 := ⟨4,false::(rep p (ones xs) ++ base),mark ++ enc z u xs ++ u⟩

theorem loopCostPos (k n : Nat) : 0 < loopCost k n := by
  cases n <;> simp only [loopCost] <;> omega

theorem closed (xs : List Bool) : ∃ t ys, 0 < t ∧ run0 table t (sec xs) = some (sec ys) := by
  rcases shape xs with ⟨k,ys,rfl⟩ | ⟨k,rfl⟩
  · cases k with
    | zero =>
      refine ⟨18,true::ys,by decide,?_⟩
      simpa only [sec,rep,ones,enc,List.nil_append,List.append_assoc] using stop0 (rep p (ones ys)++base) (enc z u ys++u)
    | succ k =>
      refine ⟨6+loopCost 1 k,rep [false] (k+1)++true::ys,by omega,?_⟩
      simp only [sec,ones_append,ones_ones,ones_zeros,ones,enc_append,enc_ones,enc_zeros,enc,Nat.zero_add]
      rw [rep_add p (k+1) (ones ys)]
      simpa only [List.append_assoc,rep,rep_snoc] using stopSucc k (rep p (ones ys)++base) (enc z u ys++u)
  · refine ⟨6+loopCost 1 k,rep [false] (k+1),by omega,?_⟩
    simpa only [sec,ones_ones,ones_zeros,enc_ones,enc_zeros,rep,List.nil_append,List.cons_append,ones,enc] using overflow k base

theorem never (M : Machine) (hm : compatible table M) : NeverHalts M :=
  BB6.Agent8Raw54.RAClosed.neverOfSection table (List Bool) sec [] 37 (by rfl) closed M hm
#print axioms never
end BB6.Agent8Raw54.ZeroRB.M51
