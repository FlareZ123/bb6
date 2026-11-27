import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw47ParityTriple
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | ra
  | rc
  | lc
  deriving DecidableEq

def ctr (v : Kind) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => match v with
    | .ra => some (some ⟨false,true,0⟩)
    | .rc => some (some ⟨false,true,2⟩)
    | .lc => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def d0 : List Bool := [true,false]
def d1 : List Bool := [true,true,true,false]
def q4 : List Bool := [true,true,true,true]
def zeros (n : Nat) : List Bool := rep [false] n

def pack : List Bool → List Bool
  | [] => []
  | false::w => d0 ++ pack w
  | true::w => d1 ++ pack w

def cfg (z : Nat) (w : List Bool) : Z0 := ⟨0,zeros z,pack w⟩

def detour : Kind → Nat
  | .ra => 2
  | .rc => 22
  | .lc => 24

theorem packZeros (n : Nat) (w : List Bool) :
    pack (List.replicate n false ++ w) = rep d0 n ++ pack w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,pack,rep,ih,List.append_assoc]

theorem packOnes (n : Nat) (w : List Bool) :
    pack (List.replicate n true ++ w) = rep d1 n ++ pack w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,pack,rep,ih,List.append_assoc]

theorem allZeros (n : Nat) : pack (List.replicate n false) = rep d0 n := by
  simpa only [List.append_nil,pack] using packZeros n []

theorem allOnes (n : Nat) : pack (List.replicate n true) = rep d1 n := by
  simpa only [List.append_nil,pack] using packOnes n []

theorem repDouble (P : List Bool) (n : Nat) :
    rep P (2*n) = rep (P++P) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ]
    change P ++ (P ++ rep P (2*n)) = (P++P) ++ rep (P++P) n
    rw [ih,List.append_assoc]

theorem repOdd (P : List Bool) (n : Nat) :
    rep P (2*n+1) = rep (P++P) n ++ P := by
  change P ++ rep P (2*n) = _
  rw [← rep_snoc P (2*n),repDouble]

-- For a positive run the implicit scanned blank can be supplied explicitly.
theorem padRun (v : Kind) (n z : Nat) (R : List Bool) (hn : 0<n) :
    run0 (ctr v) n ⟨0,zeros z,R⟩ =
      run0 (ctr v) n ⟨0,[false] ++ zeros (z-1),R⟩ := by
  cases z with
  | zero =>
    cases n with
    | zero => omega
    | succ n => rfl
  | succ z => rfl

-- Each pair of zero digits 10 10 contributes four left ones.
theorem scanPairs (v : Kind) (j : Nat) (L R : List Bool) :
    run0 (ctr v) (4*j) ⟨0,[false] ++ L,rep (d0++d0) j ++ R⟩ =
      some ⟨0,[false] ++ rep q4 j ++ L,R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using
    sweepR (ctr v) 0 [false] [] (d0++d0) q4 4 (by intro L R; rfl) j L R

-- Four left ones are converted into a right digit 1110.
theorem sweepThree (v : Kind) (j z : Nat) (R : List Bool) :
    run0 (ctr v) (4*j) ⟨0,[true,true,true] ++ rep q4 j ++ zeros z,R⟩ =
      some ⟨0,[true,true,true] ++ zeros z,rep d1 j ++ R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using
    sweepL (ctr v) 0 [true,true,true] [] q4 d1 4 (by intro L R; rfl) j (zeros z) R

theorem sweepOne (v : Kind) (j z : Nat) (R : List Bool) :
    run0 (ctr v) (4*j) ⟨0,[true] ++ rep q4 j ++ zeros z,R⟩ =
      some ⟨0,[true] ++ zeros z,rep d1 j ++ R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using
    sweepL (ctr v) 0 [true] [] q4 d1 4 (by intro L R; rfl) j (zeros z) R

theorem terminalThree (v : Kind) (z : Nat) (R : List Bool) :
    ∃ z', run0 (ctr v) 6 ⟨0,[true,true,true] ++ zeros z,R⟩ =
      some ⟨0,zeros z',d0 ++ R⟩ := by
  cases z with
  | zero => exact ⟨2,rfl⟩
  | succ z => exact ⟨z+2,rfl⟩

-- The next bit after the first 1110 must be 1. This frame is guaranteed
-- in the odd branch because it always has an additional digit 10 or 1110.
theorem terminalOne (v : Kind) (z : Nat) (R : List Bool) :
    ∃ z', run0 (ctr v) (detour v) ⟨0,[true] ++ zeros z,d1 ++ [true] ++ R⟩ =
      some ⟨0,zeros z',d1 ++ [true] ++ R⟩ := by
  cases v with
  | ra =>
    cases z with
    | zero => exact ⟨2,rfl⟩
    | succ z => exact ⟨z+2,rfl⟩
  | rc =>
    cases z with
    | zero => exact ⟨2,rfl⟩
    | succ z => exact ⟨z+2,rfl⟩
  | lc =>
    cases z with
    | zero => exact ⟨3,rfl⟩
    | succ z =>
      cases z with
      | zero => exact ⟨3,rfl⟩
      | succ z => exact ⟨z+3,rfl⟩

theorem terminalWord (v : Kind) (j z : Nat) (R : List Bool) :
    ∃ z', run0 (ctr v) (detour v) ⟨0,[true] ++ zeros z,rep d1 (j+1) ++ d0 ++ R⟩ =
      some ⟨0,zeros z',rep d1 (j+1) ++ d0 ++ R⟩ := by
  cases j with
  | zero =>
    obtain ⟨z',h⟩ := terminalOne v z ([false] ++ R)
    exact ⟨z',by simpa only [rep,d0,d1,List.append_assoc,List.nil_append,List.cons_append] using h⟩
  | succ j =>
    obtain ⟨z',h⟩ := terminalOne v z ([true,true,false] ++ rep d1 j ++ d0 ++ R)
    exact ⟨z',by simpa only [rep,d0,d1,List.append_assoc,List.nil_append,List.cons_append] using h⟩

theorem evenStep (v : Kind) (j z : Nat) (R : List Bool) :
    ∃ z', run0 (ctr v) (8*j+8) ⟨0,zeros z,rep (d0++d0) j ++ d1 ++ R⟩ =
      some ⟨0,zeros z',d0 ++ rep d1 j ++ d0 ++ R⟩ := by
  have h1 := scanPairs v j (zeros (z-1)) (d1 ++ R)
  have h2 : run0 (ctr v) 2 ⟨0,[false] ++ rep q4 j ++ zeros (z-1),d1 ++ R⟩ =
      some ⟨0,[true,true,true] ++ rep q4 j ++ zeros (z-1),d0 ++ R⟩ := rfl
  have h3 := sweepThree v j (z-1) (d0 ++ R)
  obtain ⟨z',h4⟩ := terminalThree v (z-1) (rep d1 j ++ (d0 ++ R))
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 4*j+2+4*j+6=8*j+8 by omega] at H
  refine ⟨z',?_⟩
  rw [padRun v (8*j+8) z _ (by omega)]
  simpa only [List.append_assoc] using H

theorem oddStep (v : Kind) (j z : Nat) (R : List Bool) :
    ∃ z', run0 (ctr v) (8*j+8+detour v)
        ⟨0,zeros z,rep (d0++d0) j ++ d0 ++ d1 ++ R⟩ =
      some ⟨0,zeros z',rep d1 (j+1) ++ d0 ++ R⟩ := by
  have h1 := scanPairs v j (zeros (z-1)) (d0 ++ d1 ++ R)
  have h2 : run0 (ctr v) 4 ⟨0,[false] ++ rep q4 j ++ zeros (z-1),d0 ++ d1 ++ R⟩ =
      some ⟨0,[true] ++ rep q4 (j+1) ++ zeros (z-1),d0 ++ R⟩ := rfl
  have h3 := sweepOne v (j+1) (z-1) (d0 ++ R)
  obtain ⟨z',h4⟩ := terminalWord v j (z-1) R
  have h3' : run0 (ctr v) (4*(j+1))
      ⟨0,[true] ++ rep q4 (j+1) ++ zeros (z-1),d0 ++ R⟩ =
      some ⟨0,[true] ++ zeros (z-1),rep d1 (j+1) ++ d0 ++ R⟩ := by
    simpa only [List.append_assoc] using h3
  have H := join0 (join0 (join0 h1 h2) h3') h4
  rw [show 4*j+4+4*(j+1)+detour v=8*j+8+detour v by omega] at H
  refine ⟨z',?_⟩
  rw [padRun v (8*j+8+detour v) z _ (by omega)]
  simpa only [List.append_assoc] using H

theorem resetStep (v : Kind) (j z : Nat) :
    run0 (ctr v) (8*j+13) ⟨0,zeros z,rep (d0++d0) j⟩ =
      some ⟨0,zeros (z-1),rep d1 (j+1)⟩ := by
  have h1 : run0 (ctr v) (4*j) ⟨0,[false] ++ zeros (z-1),rep (d0++d0) j⟩ =
      some ⟨0,[false] ++ rep q4 j ++ zeros (z-1),[]⟩ := by
    simpa only [List.append_nil] using scanPairs v j (zeros (z-1)) []
  have h2 : run0 (ctr v) 9 ⟨0,[false] ++ rep q4 j ++ zeros (z-1),[]⟩ =
      some ⟨0,rep q4 (j+1) ++ zeros (z-1),[]⟩ := rfl
  have h3 : run0 (ctr v) (4*(j+1)) ⟨0,rep q4 (j+1) ++ zeros (z-1),[]⟩ =
      some ⟨0,zeros (z-1),rep d1 (j+1)⟩ := by
    simpa only [List.nil_append,List.append_nil] using
      sweepL (ctr v) 0 [] [] q4 d1 4 (by intro L R; rfl) (j+1) (zeros (z-1)) []
  have H := join0 (join0 h1 h2) h3
  rw [show 4*j+9+4*(j+1)=8*j+13 by omega] at H
  rw [padRun v (8*j+13) z _ (by omega)]
  exact H

def countZeros : List Bool → Nat
  | [] => 0
  | false::w => 1+countZeros w
  | true::w => countZeros w

def Good (w : List Bool) : Prop := countZeros w % 2 = 0

theorem countPadZeros (n : Nat) (w : List Bool) :
    countZeros (List.replicate n false ++ w)=n+countZeros w := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.cons_append,countZeros,ih]; omega

theorem countPadOnes (n : Nat) (w : List Bool) :
    countZeros (List.replicate n true ++ w)=countZeros w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,countZeros,ih]

theorem countAllZeros (n : Nat) : countZeros (List.replicate n false)=n := by
  simpa only [List.append_nil,countZeros,Nat.add_zero] using countPadZeros n []

theorem countAllOnes (n : Nat) : countZeros (List.replicate n true)=0 := by
  simpa only [List.append_nil,countZeros] using countPadOnes n []

theorem zerosOrOne (w : List Bool) :
    (∃ n, w=List.replicate n false) ∨
      ∃ n s, w=List.replicate n false ++ true::s := by
  induction w with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b w ih =>
    cases b
    · rcases ih with ⟨n,rfl⟩|⟨n,s,rfl⟩
      · exact Or.inl ⟨n+1,rfl⟩
      · exact Or.inr ⟨n+1,s,rfl⟩
    · exact Or.inr ⟨0,w,rfl⟩

theorem goodStep (v : Kind) (z : Nat) (w : List Bool) (hg : Good w) :
    ∃ z' w' t, 0<t ∧ Good w' ∧ run0 (ctr v) t (cfg z w)=some (cfg z' w') := by
  rcases zerosOrOne w with ⟨n,rfl⟩|⟨n,s,rfl⟩
  · have he : n%2=0 := by simpa only [Good,countAllZeros] using hg
    obtain ⟨j,hj⟩ : ∃ j, n=2*j := ⟨n/2,by omega⟩
    subst n
    refine ⟨z-1,List.replicate (j+1) true,8*j+13,by omega,?_,?_⟩
    · simp only [Good,countAllOnes,Nat.zero_mod]
    · simpa only [cfg,allZeros,allOnes,repDouble] using resetStep v j z
  · obtain ⟨j,hj⟩ : ∃ j, n=2*j ∨ n=2*j+1 := ⟨n/2,by omega⟩
    rcases hj with hj|hj
    · subst n
      obtain ⟨z',h⟩ := evenStep v j z (pack s)
      refine ⟨z',false::(List.replicate j true ++ false::s),8*j+8,by omega,?_,?_⟩
      · simp only [Good,countPadZeros,countPadOnes,countZeros] at hg ⊢
        omega
      · simpa only [cfg,packZeros,packOnes,pack,repDouble,List.append_assoc] using h
    · subst n
      obtain ⟨z',h⟩ := oddStep v j z (pack s)
      refine ⟨z',List.replicate (j+1) true ++ false::s,8*j+8+detour v,by omega,?_,?_⟩
      · simp only [Good,countPadZeros,countPadOnes,countZeros] at hg ⊢
        omega
      · simpa only [cfg,packZeros,packOnes,pack,repOdd,List.append_assoc] using h

theorem arbitrarilyLive (v : Kind) (n : Nat) :
    ∃ z w t, n≤t ∧ Good w ∧ run0 (ctr v) t ⟨0,[],[]⟩=some (cfg z w) := by
  induction n with
  | zero => exact ⟨0,[],0,by omega,by rfl,rfl⟩
  | succ n ih =>
    obtain ⟨z,w,t,ht,hg,hr⟩ := ih
    obtain ⟨z',w',u,hu,hg',hs⟩ := goodStep v z w hg
    exact ⟨z',w',t+u,by omega,hg',join0 hr hs⟩

theorem never (v : Kind) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m := by
  intro n
  obtain ⟨z,w,t,ht,_,hr⟩ := arbitrarilyLive v n
  have hz : (Agent50Zipper.zrun (ctr v) t start).map project = some (cfg z w) :=
    (run_project (ctr v) t start).trans hr
  cases h : Agent50Zipper.zrun (ctr v) t start with
  | none => simp [h] at hz
  | some a =>
    have H := Agent50Zipper.zrun_sound (ctr v) m hm t start a h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms evenStep
#print axioms oddStep
#print axioms resetStep
#print axioms goodStep
#print axioms never
end BB6.Agent12Raw47ParityTriple
