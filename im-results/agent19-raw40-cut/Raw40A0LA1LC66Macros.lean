import SweepPumping
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Raw40.Leaf66Macros
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n
def W (n : Nat) : List Bool := rep [false] n
def A (L R : List Bool) : Z0 := ⟨0,false::L,R⟩

theorem rep_add_local (w : List Bool) (a b : Nat) :
    rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp [rep,ih,List.append_assoc]

theorem O_add (a b : Nat) : O (a+b) = O a ++ O b := rep_add_local _ _ _
theorem W_add (a b : Nat) : W (a+b) = W a ++ W b := rep_add_local _ _ _

theorem fOne (L R : List Bool) :
    run0 table 1 ⟨5,[true]++L,[]++[true]++R⟩ =
      some ⟨5,[true]++[true]++L,[]++R⟩ := by rfl

theorem cOne (L R : List Bool) :
    run0 table 1 ⟨2,[]++[true]++L,[]++R⟩ =
      some ⟨2,[]++L,[]++[true]++R⟩ := by rfl

theorem aOne (L R : List Bool) :
    run0 table 1 ⟨0,[]++[true]++L,[]++R⟩ =
      some ⟨0,[]++L,[]++[false]++R⟩ := by rfl

-- b=n+3. The scanned cell is represented by the leading false in A.
theorem lead (n : Nat) (L R : List Bool) :
    run0 table (n+5) (A L (O (n+3)++[false,false]++R)) =
      some (A (O (n+2)++[false,false,true]++L) R) := by
  have h1 : run0 table 3 (A L (O (n+3)++[false,false]++R)) =
      some ⟨5,[true,false,false,true]++L,O n++[false,false]++R⟩ := by rfl
  have h2 : run0 table n ⟨5,[true,false,false,true]++L,O n++[false,false]++R⟩ =
      some ⟨5,[true]++O n++[false,false,true]++L,[false,false]++R⟩ := by
    simpa only [O,List.nil_append,List.append_assoc,List.cons_append,Nat.one_mul] using
      (sweepR table 5 [true] [] [true] [true] 1 fOne n ([false,false,true]++L) ([false,false]++R))
  have h3 : run0 table 2 ⟨5,[true]++O n++[false,false,true]++L,[false,false]++R⟩ =
      some (A (O (n+2)++[false,false,true]++L) R) := by rfl
  have H := join0 (join0 h1 h2) h3
  simpa only [show 3+n+2=n+5 by omega] using H

theorem merge (k : Nat) (L R : List Bool) :
    run0 table (k+7) (A (O k++false::L) ([false,true]++R)) =
      some (A L (O (k+3)++R)) := by
  have h1 : run0 table 2 (A (O k++false::L) ([false,true]++R)) =
      some ⟨2,O (k+3)++false::L,R⟩ := by rfl
  have h2 : run0 table (k+3) ⟨2,O (k+3)++false::L,R⟩ =
      some ⟨2,false::L,O (k+3)++R⟩ := by
    simpa only [O,List.nil_append,Nat.one_mul] using
      (sweepL table 2 [] [] [true] [true] 1 cOne (k+3) (false::L) R)
  have h3 : run0 table 2 ⟨2,false::L,O (k+3)++R⟩ =
      some (A L (O (k+3)++R)) := by rfl
  have H := join0 (join0 h1 h2) h3
  simpa only [show 2+(k+3)+2=k+7 by omega] using H

theorem erase (k : Nat) (L R : List Bool) :
    run0 table (k+7) (A (O k++false::L) ([false,false,false]++R)) =
      some (A L (W (k+1)++[true,true,true]++R)) := by
  have h1 : run0 table 6 (A (O k++false::L) ([false,false,false]++R)) =
      some ⟨0,O (k+1)++false::L,[true,true,true]++R⟩ := by rfl
  have h2 : run0 table (k+1) ⟨0,O (k+1)++false::L,[true,true,true]++R⟩ =
      some (A L (W (k+1)++[true,true,true]++R)) := by
    simpa only [O,W,A,List.nil_append,List.append_assoc,Nat.one_mul] using
      (sweepL table 0 [] [] [true] [false] 1 aOne (k+1) (false::L) ([true,true,true]++R))
  have H := join0 h1 h2
  simpa only [show 6+(k+1)=k+7 by omega] using H

-- b=n+4, c+1 positive. The framed lemma does not assume anything
-- about the finite tails L,R, so it also covers arbitrary longer stacks.
theorem joinGap (n k c : Nat) (L R : List Bool) :
    run0 table (2*n+16) (A (O k++L) (O (n+4)++[false,false,false]++O (c+1)++R)) =
      some (A (false::O (k+1)++L) (O (n+c+6)++R)) := by
  have h1 := lead (n+1) (O k++L) ([false,true]++O c++R)
  have h2 := merge (n+3) ([false,true]++O k++L) (O c++R)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2
  have H := join0 h1 h2
  have e : (n+1+5)+(n+3+7)=2*n+16 := by omega
  have f : n+6+c=n+c+6 := by omega
  have hw : O (n+6)++(O c++R) = O (n+c+6)++R := by
    rw [← List.append_assoc,← O_add,f]
  rw [← e]
  simp only [List.append_assoc]
  rw [← hw]
  simpa only [O,rep,List.append_assoc,List.cons_append,List.nil_append] using H

theorem splitGap (n k : Nat) (L R : List Bool) :
    run0 table (2*n+k+31) (A (O k++false::L) (O (n+4)++[false,false,false,false,false]++R)) =
      some (A L (O (k+6)++W (n+1)++[true,true,true]++R)) := by
  have h1 := lead (n+1) (O k++false::L) ([false,false,false]++R)
  have h2 := erase (n+3) ([false,true]++O k++false::L) R
  have h3 := erase 0 ([true]++O k++false::L) (W (n+1)++[true,true,true]++R)
  have h4 := merge (k+1) L ([true,true]++W (n+1)++[true,true,true]++R)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2 h3 h4
  have H12 := join0 h1 h2
  have H123 := join0 H12 (show run0 table (0+7) (A ([false,true]++O k++false::L) (W (n+4)++[true,true,true]++R)) = _ from by
    simpa only [O,W,rep,List.append_assoc,List.cons_append,List.nil_append] using h3)
  have H := join0 H123 (show run0 table (k+1+7) (A ([true]++O k++false::L) (W 1++[true,true,true]++W (n+1)++[true,true,true]++R)) = _ from by
    simpa only [O,W,rep,List.append_assoc,List.cons_append,List.nil_append] using h4)
  have e : (n+1+5)+(n+3+7)+(0+7)+(k+1+7)=2*n+k+31 := by omega
  have hw : O (k+4)++([true,true]++(W (n+1)++([true,true,true]++R))) =
      O (k+6)++(W (n+1)++([true,true,true]++R)) := by
    rw [← List.append_assoc]
    change (O (k+4)++O 2)++_ = _
    rw [← O_add]
  rw [← e]
  simp only [List.append_assoc]
  rw [← hw]
  simpa only [O,W,rep,List.append_assoc,List.cons_append,List.nil_append] using H

#print axioms lead
#print axioms merge
#print axioms erase
#print axioms joinGap
#print axioms splitGap
end BB6.Agent19Raw40.Leaf66Macros
