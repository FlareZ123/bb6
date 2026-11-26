import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RBCounterPair
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,v,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => if v then some (some ⟨false,false,3⟩) else some (some ⟨true,false,0⟩)
  | _,_ => none

def M : List Bool := [true,true,false,false]
def P : List Bool := [false,true,true,true]
def B : List Bool := [false,true,true,true,true,true,true]
def Z : List Bool := [false]
def O : List Bool := [true]
def base : List Bool := rep Z 8

def sec (n : Nat) (R : List Bool) : Z0 := ⟨4,[],base ++ rep M n ++ R⟩
def frame (n : Nat) (R : List Bool) : Z0 := ⟨0,[false,true] ++ rep P n ++ B,false::R⟩

theorem rep_add (X : List Bool) (a b : Nat) : rep X (a+b) = rep X a ++ rep X b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem prefixScan (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (23+4*n) (sec n R) = some (frame n R) := by
  have a : run0 (table v) 23 (sec n R) = some ⟨0,[false,true]++B,false::(rep M n++R)⟩ := by cases v <;> rfl
  have b := sweepR (table v) 0 [false,true] [false] M P 4 (by intro L R; cases v <;> rfl) n B R
  simpa only [frame,List.append_assoc,List.cons_append,List.nil_append] using join0 a b

theorem unwind (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (10*n+13) ⟨4,rep P n++B,[false,false,false]++R⟩ = some (sec n ([true,true]++R)) := by
  have c : [true,true] ++ rep [false,false,true,true] n = rep M n ++ [true,true] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change [true,true]++([false,false,true,true]++rep [false,false,true,true] n) = M++rep M n++[true,true]
      rw [← List.append_assoc]
      change M++([true,true]++rep [false,false,true,true] n) = _
      rw [ih,List.append_assoc]
  have a := sweepL (table v) 4 [] [false,false,false] P [false,false,true,true] 10 (by intro L R; cases v <;> rfl) n B R
  have b : run0 (table v) 13 ⟨4,B,[false,false,false]++rep [false,false,true,true] n++R⟩ =
      some ⟨4,[],base++[true,true]++rep [false,false,true,true] n++R⟩ := by cases v <;> rfl
  have H := join0 (by simpa only [List.nil_append,List.append_assoc] using a) (by simpa only [List.append_assoc] using b)
  have d : [true,true] ++ (rep [false,false,true,true] n ++ R) = rep M n ++ ([true,true]++R) := by
    rw [← List.append_assoc,c,List.append_assoc]
  simpa only [sec,List.append_assoc,d] using H

theorem epoch (v : Bool) (n k t : Nat) (U V R : List Bool)
    (h : ∀ L S : List Bool, run0 (table v) t ⟨0,[false,true]++rep P k++L,false::(U++S)⟩ =
      some ⟨4,L,[false,false,false]++V++S⟩) :
    run0 (table v) (23+4*(k+n)+t+(10*n+13)) (sec (k+n) (U++R)) = some (sec n ([true,true]++V++R)) := by
  have a := prefixScan v (k+n) (U++R)
  have b := h (rep P n++B) R
  have a' : run0 (table v) (23+4*(k+n)) (sec (k+n) (U++R)) =
      some ⟨0,[false,true]++rep P k++(rep P n++B),false::(U++R)⟩ := by
    simpa only [frame,rep_add,List.append_assoc] using a
  have b' : run0 (table v) t ⟨0,[false,true]++rep P k++(rep P n++B),false::(U++R)⟩ =
      some ⟨4,rep P n++B,[false,false,false]++(V++R)⟩ := by simpa only [List.append_assoc] using b
  exact join0 (join0 a' b') (by simpa only [List.append_assoc] using unwind v n (V++R))

def enc : List Bool → List Bool
  | [] => []
  | b::w => b::b::enc w

theorem sec_shift (n : Nat) (R : List Bool) : sec n (M++R) = sec (n+1) R := by
  simp only [sec,rep_add,List.append_assoc]
  rfl

namespace ID19
def p0 : List Bool := enc [false,false,false,false,false,false,false,false]
def p1 : List Bool := enc [true,true,false,false,false,false,false,false,false]
def p2 : List Bool := enc [false,false,true,false,false,false,false,false]
def p3 : List Bool := enc [true,true,false,true,false,false,false,false,false]
def p4 : List Bool := enc [false,false,false,true,true,false,false,false]
def p5 : List Bool := enc [true,true,false,false,true,true,false,false,false]
def p6 : List Bool := enc [false,false,true,true,true,false,false,false]
def p7 : List Bool := enc [true,true,false,true,true,true,false,false,false]

theorem phase0 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+44) (sec n (p0++R)) = some (sec n (p1++R)) := by
  have H := epoch false n 0 8 p0 [true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+8+(10*n+13)=14*n+44 by omega] at H
  rw [Nat.zero_add] at H
  exact H

theorem phase1 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+60) (sec n (p1++R)) = some (sec (n+1) (p2++R)) := by
  have H := epoch false n 0 24 p1 [false,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+24+(10*n+13)=14*n+60 by omega] at H
  rw [Nat.zero_add] at H
  change run0 (table false) (14*n+60) (sec n (p1++R)) = some (sec n (M++(p2++R))) at H
  rw [sec_shift] at H
  exact H

theorem phase2 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+44) (sec n (p2++R)) = some (sec n (p3++R)) := by
  have H := epoch false n 0 8 p2 [true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+8+(10*n+13)=14*n+44 by omega] at H
  rw [Nat.zero_add] at H
  exact H

theorem phase3 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+74) (sec n (p3++R)) = some (sec (n+1) (p4++R)) := by
  have H := epoch false n 0 38 p3 [false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+38+(10*n+13)=14*n+74 by omega] at H
  rw [Nat.zero_add] at H
  change run0 (table false) (14*n+74) (sec n (p3++R)) = some (sec n (M++(p4++R))) at H
  rw [sec_shift] at H
  exact H

theorem phase4 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+44) (sec n (p4++R)) = some (sec n (p5++R)) := by
  have H := epoch false n 0 8 p4 [true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+8+(10*n+13)=14*n+44 by omega] at H
  rw [Nat.zero_add] at H
  exact H

theorem phase5 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+60) (sec n (p5++R)) = some (sec (n+1) (p6++R)) := by
  have H := epoch false n 0 24 p5 [false,false,false,false,false,false,true,true,true,true,true,true,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+24+(10*n+13)=14*n+60 by omega] at H
  rw [Nat.zero_add] at H
  change run0 (table false) (14*n+60) (sec n (p5++R)) = some (sec n (M++(p6++R))) at H
  rw [sec_shift] at H
  exact H

theorem phase6 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+44) (sec n (p6++R)) = some (sec n (p7++R)) := by
  have H := epoch false n 0 8 p6 [true,true,false,false,true,true,true,true,true,true,false,false,false,false,false,false] R (by intro L S; rfl)
  rw [show 23+4*(0+n)+8+(10*n+13)=14*n+44 by omega] at H
  rw [Nat.zero_add] at H
  exact H

theorem phase7 (n : Nat) (R : List Bool) :
    run0 (table false) (14*n+116) (sec (n+1) (p7++R)) = some (sec (n+1) (p0++M++R)) := by
  have H := epoch false n 1 76 p7 [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false] R (by intro L S; rfl)
  rw [show 23+4*(1+n)+76+(10*n+13)=14*n+116 by omega] at H
  rw [show 1+n=n+1 by omega] at H
  change run0 (table false) (14*n+116) (sec (n+1) (p7++R)) = some (sec n (M++(p0++M++R))) at H
  rw [sec_shift] at H
  exact H

theorem cycle (n : Nat) (R : List Bool) :
    run0 (table false) (112*n+640) (sec n (p0++R)) = some (sec (n+3) (p0++M++R)) := by
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R))
    (phase2 (n+1) R)) (phase3 (n+1) R)) (phase4 (n+2) R)) (phase5 (n+2) R)) (phase6 (n+3) R)) (phase7 (n+2) R)
  rw [show 14*n+44+(14*n+60)+(14*(n+1)+44)+(14*(n+1)+74)+(14*(n+2)+44)+(14*(n+2)+60)+(14*(n+3)+44)+(14*(n+2)+116)=112*n+640 by omega] at H
  exact H

def family (k : Nat) : Z0 := sec (3*k+3) (p0++rep M k++[true,true])
theorem first : run0 (table false) 640 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 (table false) (112*(3*k+3)+640) (family k) = some (family (k+1)) := by
  have H := cycle (3*k+3) (rep M k++[true,true])
  simpa only [family,show 3*k+3+3=3*(k+1)+3 by omega,rep,List.append_assoc] using H

theorem never (m : Machine) (hm : compatible (table false) m) : NeverHalts m :=
  never_of_growth (table false) family 640 (fun k => 112*(3*k+3)+640) first (by intro k; omega) growth m hm
#print axioms never
end ID19

namespace ID23

def blk (k : Nat) : List Bool := false::rep O (2*k+1)
inductive Stack where
  | base (k : Nat)
  | push (k : Nat) (s : Stack)

def stack : Stack → List Bool
  | .base k => blk (k+3)
  | .push k s => blk k ++ stack s

def grow (d : Nat) : Stack → Stack
  | .base k => .base (k+d)
  | .push k s => .push (k+d) s

def scan (n : Nat) (s : Stack) (w : List Bool) : Z0 :=
  ⟨0,w.headD false::true::(stack s ++ rep P n ++ B),(enc w).tail⟩

theorem enc_append (w u : List Bool) : enc (w++u) = enc w++enc u := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append,enc,ih]

theorem enc_zeros (k : Nat) (w : List Bool) : enc (List.replicate k false ++ w) = rep Z (2*k) ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,enc,ih]
    rfl

theorem drainBlock (k : Nat) (L : List Bool) (w : List Bool) :
    run0 (table true) (2*k+8) ⟨4,blk k++L,false::false::false::enc w⟩ =
      some ⟨4,L,false::false::false::enc (List.replicate k false ++ true::w)⟩ := by
  have a : run0 (table true) 6 ⟨4,blk k++L,false::false::false::enc w⟩ =
      some ⟨4,rep O (2*k+2)++L,false::true::true::enc w⟩ := by rfl
  have b := sweepL (table true) 4 [] [] O Z 1 (by intro L R; rfl) (2*k+2) L (false::true::true::enc w)
  simp only [List.nil_append,Nat.one_mul] at b
  have H := join0 a b
  change run0 (table true) _ _ = some ⟨4,L,rep Z (2*k+2)++(rep Z 1++true::true::enc w)⟩ at H
  rw [show 6+(2*k+2)=2*k+8 by omega,← List.append_assoc,← rep_add Z (2*k+2) 1,show 2*k+2+1=3+2*k by omega,rep_add Z 3 (2*k)] at H
  simpa only [enc_zeros,enc,List.append_assoc,show rep Z 3 = [false,false,false] by rfl,List.cons_append,List.nil_append] using H

theorem drain (n : Nat) (s : Stack) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t ⟨4,stack s++rep P n++B,false::false::false::enc w⟩ =
      some (sec (n+1) (enc (false::false::u))) := by
  induction s generalizing w with
  | base k =>
    have a := drainBlock (k+3) (rep P n++B) w
    have b := unwind true n (enc (List.replicate (k+3) false ++ true::w))
    have H := join0 a b
    refine ⟨2*(k+3)+8+(10*n+13),by omega,List.replicate k false++true::w,?_⟩
    have e : [true,true] ++ enc (List.replicate (k+3) false ++ true::w) = M ++ enc (false::false::(List.replicate k false++true::w)) := by
      rfl
    rw [e,sec_shift] at H
    simpa only [stack,List.append_assoc] using H
  | push k s ih =>
    have a := drainBlock k (stack s++rep P n++B) w
    obtain ⟨t,ht,u,b⟩ := ih (List.replicate k false++true::w)
    refine ⟨2*k+8+t,by omega,u,?_⟩
    simpa only [stack,List.append_assoc] using join0 a b

theorem raw00 (L : List Bool) (w : List Bool) :
    run0 (table true) 8 ⟨0,false::true::L,false::false::false::enc w⟩ = some ⟨4,L,false::false::false::true::true::enc w⟩ := by rfl

theorem rawNil (L : List Bool) : run0 (table true) 8 ⟨0,false::true::L,[]⟩ = some ⟨4,L,[false,false,false,true,true]⟩ := by rfl

theorem rawF (L : List Bool) : run0 (table true) 8 ⟨0,false::true::L,[false]⟩ = some ⟨4,L,[false,false,false,true,true]⟩ := by rfl

theorem raw01 (L : List Bool) (w : List Bool) :
    run0 (table true) 4 ⟨0,false::true::L,false::true::true::enc w⟩ =
      some ⟨0,w.headD false::true::(blk 1++L),(enc w).tail⟩ := by cases w <;> rfl

theorem raw10 (k : Nat) (L : List Bool) (w : List Bool) :
    run0 (table true) 16 ⟨0,true::true::(blk k++L),true::false::false::enc w⟩ =
      some ⟨0,w.headD false::true::(blk (k+2)++L),(enc w).tail⟩ := by cases w <;> rfl

theorem rawT (k : Nat) (L : List Bool) :
    run0 (table true) 16 ⟨0,true::true::(blk k++L),[true]⟩ =
      some ⟨0,false::true::(blk (k+2)++L),[]⟩ := by rfl

theorem raw11 (k : Nat) (L : List Bool) (w : List Bool) :
    run0 (table true) 10 ⟨0,true::true::(blk k++L),true::true::true::enc w⟩ =
      some ⟨0,w.headD false::true::(blk 0++blk (k+1)++L),(enc w).tail⟩ := by cases w <;> rfl

theorem scan00 (n : Nat) (s : Stack) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (scan n s (false::false::w)) = some (sec (n+1) (enc (false::false::u))) := by
  have a := raw00 (stack s++rep P n++B) w
  obtain ⟨t,ht,u,b⟩ := drain n s (true::w)
  exact ⟨8+t,by omega,u,join0 a b⟩

theorem scanNil (n : Nat) (s : Stack) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (scan n s []) = some (sec (n+1) (enc (false::false::u))) := by
  obtain ⟨t,ht,u,b⟩ := drain n s [true]
  exact ⟨8+t,by omega,u,join0 (rawNil (stack s++rep P n++B)) b⟩

theorem scanF (n : Nat) (s : Stack) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (scan n s [false]) = some (sec (n+1) (enc (false::false::u))) := by
  obtain ⟨t,ht,u,b⟩ := drain n s [true]
  exact ⟨8+t,by omega,u,join0 (rawF (stack s++rep P n++B)) b⟩

theorem scan01 (n : Nat) (s : Stack) (w : List Bool) :
    run0 (table true) 4 (scan n s (false::true::w)) = some (scan n (.push 1 s) w) := by
  simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,List.append_assoc] using raw01 (stack s++rep P n++B) w

theorem scan10 (n : Nat) (s : Stack) (w : List Bool) :
    run0 (table true) 16 (scan n s (true::false::w)) = some (scan n (grow 2 s) w) := by
  cases s with
  | base k =>
    simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc,show k+3+2=k+2+3 by omega] using raw10 (k+3) (rep P n++B) w
  | push k s => simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc] using raw10 k (stack s++rep P n++B) w

theorem scanT (n : Nat) (s : Stack) :
    run0 (table true) 16 (scan n s [true]) = some (scan n (grow 2 s) []) := by
  cases s with
  | base k =>
    simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc,show k+3+2=k+2+3 by omega] using rawT (k+3) (rep P n++B)
  | push k s => simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc] using rawT k (stack s++rep P n++B)

theorem scan11 (n : Nat) (s : Stack) (w : List Bool) :
    run0 (table true) 10 (scan n s (true::true::w)) = some (scan n (.push 0 (grow 1 s)) w) := by
  cases s with
  | base k =>
    simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc,show k+3+1=k+1+3 by omega] using raw11 (k+3) (rep P n++B) w
  | push k s => simpa only [scan,enc,List.headD_cons,List.headD_nil,List.tail_cons,List.tail_nil,stack,grow,List.append_assoc] using raw11 k (stack s++rep P n++B) w

theorem scanAll (n fuel : Nat) (s : Stack) (w : List Bool) (hw : w.length ≤ fuel) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (scan n s w) = some (sec (n+1) (enc (false::false::u))) := by
  induction fuel generalizing s w with
  | zero =>
    cases w with
    | nil => exact scanNil n s
    | cons b w => simp at hw
  | succ fuel ih =>
    cases w with
    | nil => exact scanNil n s
    | cons b w =>
      cases w with
      | nil =>
        cases b with
        | false => exact scanF n s
        | true =>
          obtain ⟨t,ht,u,h⟩ := scanNil n (grow 2 s)
          exact ⟨16+t,by omega,u,join0 (scanT n s) h⟩
      | cons c w =>
        have hw' : w.length ≤ fuel := by simp at hw; omega
        cases b <;> cases c
        · exact scan00 n s w
        · obtain ⟨t,ht,u,h⟩ := ih (.push 1 s) w hw'
          exact ⟨4+t,by omega,u,join0 (scan01 n s w) h⟩
        · obtain ⟨t,ht,u,h⟩ := ih (grow 2 s) w hw'
          exact ⟨16+t,by omega,u,join0 (scan10 n s w) h⟩
        · obtain ⟨t,ht,u,h⟩ := ih (.push 0 (grow 1 s)) w hw'
          exact ⟨10+t,by omega,u,join0 (scan11 n s w) h⟩

theorem phase0 (n : Nat) (w : List Bool) :
    run0 (table true) (14*n+44) (sec n (enc (false::false::w))) = some (sec n (enc (true::true::false::w))) := by
  have H := epoch true n 0 8 (enc [false,false]) [true,true,false,false] (enc w) (by intro L R; rfl)
  rw [show 23+4*(0+n)+8+(10*n+13)=14*n+44 by omega,Nat.zero_add] at H
  exact H

theorem phase1 (n : Nat) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (sec n (enc (true::true::false::w))) = some (sec (n+1) (enc (false::false::u))) := by
  have a := prefixScan true n (enc (true::true::false::w))
  have b : run0 (table true) 20 (frame n (enc (true::true::false::w))) = some (scan n (.base 0) w) := by cases w <;> rfl
  obtain ⟨t,ht,u,h⟩ := scanAll n w.length (.base 0) w (by omega)
  exact ⟨23+4*n+20+t,by omega,u,join0 (join0 a b) h⟩

theorem sectionReturn (n : Nat) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 (table true) t (sec n (enc (false::false::w))) = some (sec (n+1) (enc (false::false::u))) := by
  obtain ⟨t,ht,u,h⟩ := phase1 n w
  exact ⟨14*n+44+t,by omega,u,join0 (phase0 n w) h⟩

theorem first : run0 (table true) 122 ⟨0,[],[]⟩ = some (sec 1 (enc [false,false,true,true])) := by rfl

theorem arbitrary (k : Nat) : ∃ t, k≤t ∧ ∃ n w, run0 (table true) t ⟨0,[],[]⟩ = some (sec n (enc (false::false::w))) := by
  induction k with
  | zero => exact ⟨122,by omega,1,[true,true],first⟩
  | succ k ih =>
    obtain ⟨t,ht,n,w,H⟩ := ih
    obtain ⟨s,hs,u,G⟩ := sectionReturn n w
    exact ⟨t+s,by omega,n+1,u,join0 H G⟩

theorem never (m : Machine) (hm : compatible (table true) m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,j,w,hr⟩ := arbitrary n
  have hz : (zrun (table true) t start).map project = some (sec j (enc (false::false::w))) := (run_project (table true) t start).trans hr
  cases h : zrun (table true) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table true) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms sectionReturn
#print axioms never
end ID23
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  cases v with
  | false => exact ID19.never m hm
  | true => exact ID23.never m hm

#print axioms never
end BB6.Agent8Raw54.RBCounterPair
