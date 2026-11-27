import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Doubling
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def R (n : Nat) : List Bool := rep [true,false] n
def U (n : Nat) : List Bool := rep [true,true] n

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp only [rep,ih,List.append_assoc]

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (B [] (R 2)) := by rfl

theorem first (X : List Bool) : run0 table 6 (B [] ([true,false]++X)) = some (C [false,true,true,true] X) := by rfl

theorem cone (L X : List Bool) : run0 table 2 (C ([false]++L) ([true,false]++X)) = some (C ([false,true,false]++L) X) := by rfl

theorem cscan (n : Nat) : run0 table (2*n) (C [false,true,true,true] (R n)) = some (C ([false]++R n++[true,true,true]) []) := by
  simpa only [B,C,R,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using
    (sweepR table 2 [false] [] [true,false] [true,false] 2 cone n [true,true,true] [])

theorem turn (L : List Bool) : run0 table 4 (C ([false,true,false]++L) []) = some (C ([true,true,false]++L) [true]) := by rfl

theorem raise (L : List Bool) : run0 table 20 (C ([true,true,false,true]++L) [true]) = some (B (U 4++L) []) := by rfl

theorem boneL (L X : List Bool) : run0 table 2 (B ([true,true]++L) X) = some (B L ([true,false]++X)) := by rfl

theorem bscanL (n : Nat) (L : List Bool) : run0 table (2*n) (B (U n++L) []) = some (B L (R n)) := by
  simpa only [B,R,U,List.append_nil,List.nil_append] using (sweepL table 1 [] [] [true,true] [true,false] 2 boneL n L [])

theorem boneR (L X : List Bool) : run0 table 6 (B ([false,true]++L) ([true,false]++X)) = some (B ([false,true,true,true]++L) X) := by rfl

theorem one_commute (m : Nat) : [true]++U m = U m++[true] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [U,rep,List.append_assoc,List.cons_append,List.nil_append] at ih ⊢
    exact congrArg (fun x : List Bool => true::true::x) ih

theorem bscanR (m : Nat) (L : List Bool) : run0 table (6*m) (B ([false,true]++L) (R m)) = some (B ([false]++U m++[true]++L) []) := by
  have h := sweepR table 1 [false,true] [] [true,false] [true,true] 6 boneR m L []
  have h' : [false,true]++U m++L = [false]++U m++[true]++L := by
    calc
      _ = [false]++([true]++U m)++L := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [one_commute]; simp only [List.append_assoc]
  change run0 table _ (B ([false,true]++L) (R m++[])) = some (B ([false,true]++U m++L) []) at h
  rw [List.append_nil,h'] at h
  exact h

theorem boost (L : List Bool) : run0 table 10 (B ([false,true,true]++L) []) = some (B ([true,true,true,true,true]++L) []) := by rfl

theorem boostN (m : Nat) (L : List Bool) : run0 table 10 (B ([false]++U (m+1)++L) []) = some (B ([true,true,true]++U (m+1)++L) []) := by
  simpa only [U,rep,List.append_assoc,List.cons_append,List.nil_append] using boost (U m++L)

-- Exchange three explicit leading ones plus one input one for two pairs.
theorem odd_to_even (m : Nat) (L : List Bool) : [true,true,true]++U m++[true]++L = U (m+2)++L := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [U,rep,List.append_assoc,List.cons_append] at ih ⊢
    exact congrArg (fun x : List Bool => true::true::x) ih

theorem final_even (m : Nat) : [true,true,true]++U m++[true,true,true] = U (m+3) := by
  have h := odd_to_even m [true,true]
  have h2 : U (m+3) = U (m+2)++[true,true] := by
    unfold U
    exact rep_add [true,true] (m+2) 1
  rw [h2]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

-- Remaining zero delimiters are consumed one at a time. The output exponent grows by two per delimiter.
def innerCost : Nat → Nat → Nat
  | 0,m => 6*m+10+2*(m+3)
  | k+1,m => 6*m+10+2*(m+2)+innerCost k (m+2)

theorem inner (k m : Nat) (hm : 0<m) :
    run0 table (innerCost k m) (B ([false]++R k++[true,true,true]) (R m)) = some (B [] (R (m+2*k+3))) := by
  cases m with
  | zero => omega
  | succ m =>
    induction k generalizing m with
    | zero =>
      have h1 := bscanR (m+1) [true,true]
      have h2 := boostN m [true,true,true]
      have h1' : run0 table (6*(m+1)) (B ([false]++[true,true,true]) (R (m+1))) = some (B ([false]++U (m+1)++[true,true,true]) []) := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using h1
      have h := join0 h1' h2
      rw [final_even] at h
      have h3 : run0 table (2*(m+1+3)) (B (U (m+1+3)) []) = some (B [] (R (m+1+3))) := by
        simpa only [List.append_nil] using bscanL (m+1+3) []
      have h := join0 h h3
      simpa only [innerCost,R,rep,List.nil_append,List.append_nil,Nat.mul_zero,Nat.add_zero] using h
    | succ k ih =>
      have h1 := bscanR (m+1) ([false]++R k++[true,true,true])
      have h2 := boostN m (R (k+1)++[true,true,true])
      have h1' : run0 table (6*(m+1)) (B ([false]++R (k+1)++[true,true,true]) (R (m+1))) = some (B ([false]++U (m+1)++(R (k+1)++[true,true,true])) []) := by
        simpa only [R,rep,List.append_assoc,List.cons_append,List.nil_append] using h1
      have h := join0 h1' h2
      have he : [true,true,true]++U (m+1)++(R (k+1)++[true,true,true]) = U (m+1+2)++([false]++R k++[true,true,true]) := by
        simpa only [R,rep,List.append_assoc,List.cons_append,List.nil_append] using odd_to_even (m+1) ([false]++R k++[true,true,true])
      rw [he] at h
      have h := join0 h (bscanL (m+1+2) ([false]++R k++[true,true,true]))
      have h := join0 h (ih (m+2) (by omega))
      rw [show m+2+1+2*k+3=m+1+2*(k+1)+3 by omega] at h
      simpa only [innerCost] using h

-- The outer return first converts the input to alternating left delimiters.
def cost : Nat → Nat
  | 0 => 42
  | k+1 => 6+2*(k+2)+4+20+8+innerCost k 4

theorem outer (k : Nat) : run0 table (cost k) (B [] (R (k+2))) = some (B [] (R (2*(k+2)+1))) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 := first (R (k+2))
    have h2 := cscan (k+2)
    have h := join0 h1 h2
    have h := join0 h (turn (R (k+1)++[true,true,true]))
    have h := join0 h (raise ([false]++R k++[true,true,true]))
    have h := join0 h (bscanL 4 ([false]++R k++[true,true,true]))
    have h := join0 h (inner k 4 (by decide))
    rw [show 4+2*k+3=2*(k+1+2)+1 by omega] at h
    exact h

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+3

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun n => B [] (R (index n+2))) 15 (fun n => cost (index n)) entry
  · intro n
    cases h : index n with
    | zero => decide
    | succ k => simp [cost]; omega
  · intro n
    have h := outer (index n)
    rw [show 2*(index n+2)+1=index (n+1)+2 by simp [index]; omega] at h
    exact h
  · exact hm
#print axioms never
end BB6.Agent7Raw49Doubling
