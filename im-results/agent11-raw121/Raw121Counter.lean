import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw121Counter
open BB6Coverage BB6Coverage.Agent31Pump

theorem repReplicate (b : Bool) (k n : Nat) :
    rep (List.replicate k b) n = List.replicate (k*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,List.replicate_append_replicate,show k+k*n=k*(n+1) by rw [Nat.mul_succ,Nat.add_comm]]

theorem replicateAddTail (b : Bool) (a c : Nat) (R : List Bool) :
    List.replicate a b ++ (List.replicate c b ++ R) = List.replicate (a+c) b ++ R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

abbrev U := [true]
abbrev Z := [false]
def atE (k : Nat) (S : List Bool) (n : Nat) (R : List Bool) : Z0 := ⟨4,false::(rep U (n+k)++S),R⟩
def atHead (k : Nat) (S : List Bool) (n : Nat) (R : List Bool) : Z0 := ⟨4,R.headD false::(rep U (n+k)++S),R.tail⟩
def costs (base d s : Nat) : Nat → Nat × Nat
  | 0 => (base,0)
  | n+1 => (d+s*n+(costs base d s n).2+(costs base d s n).1+1,(costs base d s n).2+(costs base d s n).1)

theorem advance_and_prefix (p : PartialMachine) (k : Nat) (S : List Bool) (base d s : Nat)
    (hbase : ∀ R, run0 p base (atE k S 0 R) = some (atHead k S 1 R))
    (hdesc : ∀ n R, run0 p (d+s*n) (atE k S (n+1) R) = some (atE k S 0 (rep Z n++true::R)))
    (hone : ∀ n R, run0 p 1 (atHead k S n (true::R)) = some (atHead k S (n+1) R))
    (n : Nat) :
    (∀ R, run0 p (costs base d s n).1 (atE k S n R) = some (atHead k S (n+1) R)) ∧
    (∀ R, run0 p (costs base d s n).2 (atE k S 0 (rep Z n++R)) = some (atE k S n R)) := by
  induction n with
  | zero => exact ⟨hbase,by intro R; rfl⟩
  | succ n ih =>
    constructor
    · intro R
      have h := join0 (join0 (join0 (hdesc n R) (ih.2 (true::R))) (ih.1 (true::R))) (hone (n+1) R)
      exact h
    · intro R
      have h := join0 (ih.2 (false::R)) (ih.1 (false::R))
      have e : rep Z n ++ false::R = rep Z (n+1) ++ R := by
        change rep Z n ++ (Z++R) = (Z++rep Z n)++R
        rw [← List.append_assoc,rep_snoc]
      rw [e] at h
      exact h


namespace M4463

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), (R)⟩ = some ⟨0, ([true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 3 ⟨0, ([true,true]) ++ (([true]) ++ ((L))), (T)⟩ = some ⟨0, ([true,true]) ++ ((L)), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨0, ([true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), ([true]) ++ ((R))⟩ = some ⟨0, ([true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true] [] [true] [false] 3 descLocal1 n (([true,true,true,true,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 24 ⟨0, ([true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (25+3*n) ⟨4, ([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+3*n+24=25+3*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false])))) = (([false,true,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 4 true) ++ ((List.replicate 1 false)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 1 false)))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false]
theorem desc (n : Nat) (R : List Bool) : run0 table (25+3*n) (atE 5 S (n+1) R) = some (atE 5 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 23 (atE 5 S 0 R) = some (atHead 5 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 5 S n (true::R)) = some (atHead 5 S (n+1) R) := by rfl

def family (n : Nat) := atE 5 S (n+1) []
def cost (n : Nat) := (costs 23 25 3 (n+1)).1

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 5 S 23 25 3 base desc one (n+1)).1 []
  rw [show n+1+1=n+1+1 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+1 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M4463

namespace M4759

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), (R)⟩ = some ⟨0, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 5 ⟨0, ([true]) ++ (([true]) ++ ((L))), (T)⟩ = some ⟨0, ([true]) ++ ((L)), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (5*n) ⟨0, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), ([true]) ++ ((R))⟩ = some ⟨0, ([true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true] [] [true] [false] 5 descLocal1 n (([true,true,true,true,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 30 ⟨0, ([true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (31+5*n) ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+5*n+30=31+5*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,false])))) = (([false,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 4 true) ++ ((List.replicate 1 false)))))) = ((List.replicate 1 false) ++ ((List.replicate 5 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 1 false)))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false]
theorem desc (n : Nat) (R : List Bool) : run0 table (31+5*n) (atE 4 S (n+1) R) = some (atE 4 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 27 (atE 4 S 0 R) = some (atHead 4 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 4 S n (true::R)) = some (atHead 4 S (n+1) R) := by rfl

def family (n : Nat) := atE 4 S (n+1) []
def cost (n : Nat) := (costs 27 31 5 (n+1)).1

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 4 S 27 31 5 base desc one (n+1)).1 []
  rw [show n+1+1=n+1+1 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+1 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M4759

namespace M4820

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false]))), (R)⟩ = some ⟨0, ([true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false]))), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 3 ⟨0, ([true,true]) ++ (([true]) ++ ((L))), (T)⟩ = some ⟨0, ([true,true]) ++ ((L)), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨0, ([true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false]))), ([true]) ++ ((R))⟩ = some ⟨0, ([true,true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true] [] [true] [false] 3 descLocal1 n (([true,true,true,true,true,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 32 ⟨0, ([true,true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (33+3*n) ⟨4, ([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+3*n+32=33+3*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false,true,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false])))) = (([false,true,true,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 5 true) ++ ((List.replicate 1 false)))))) = ((List.replicate 1 false) ++ ((List.replicate 7 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 1 false)))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false]
theorem desc (n : Nat) (R : List Bool) : run0 table (33+3*n) (atE 6 S (n+1) R) = some (atE 6 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 31 (atE 6 S 0 R) = some (atHead 6 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 6 S n (true::R)) = some (atHead 6 S (n+1) R) := by rfl

def family (n : Nat) := atE 6 S (n+3) []
def cost (n : Nat) := (costs 31 33 3 (n+3)).1

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 6 S 31 33 3 base desc one (n+3)).1 []
  rw [show n+3+1=n+1+3 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+3 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M4820

namespace M8393

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), (R)⟩ = some ⟨1, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 3 ⟨1, ([true]) ++ (([true]) ++ ((L))), (T)⟩ = some ⟨1, ([true]) ++ ((L)), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨1, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), ([true]) ++ ((R))⟩ = some ⟨1, ([true,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true] [] [true] [false] 3 descLocal1 n (([true,true,true,true,true,false,true,true,true,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 26 ⟨1, ([true,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (27+3*n) ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+3*n+26=27+3*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false])))) = (([false,true,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false,true,true,true,false])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 5 true) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((List.replicate 1 false)))))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((List.replicate 1 false)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false,true,true,true,false]
theorem desc (n : Nat) (R : List Bool) : run0 table (27+3*n) (atE 5 S (n+1) R) = some (atE 5 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 25 (atE 5 S 0 R) = some (atHead 5 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 5 S n (true::R)) = some (atHead 5 S (n+1) R) := by rfl

def family (n : Nat) := atE 5 S (n+0) []
def cost (n : Nat) := (costs 25 27 3 (n+0)).1

theorem entry : run0 table 41 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 5 S 25 27 3 base desc one (n+0)).1 []
  rw [show n+0+1=n+1+0 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+0 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 41 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M8393

namespace M9402

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), (R)⟩ = some ⟨2, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 3 ⟨2, ([true]) ++ (([true]) ++ ((L))), (T)⟩ = some ⟨2, ([true]) ++ ((L)), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2, ([true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), ([true]) ++ ((R))⟩ = some ⟨2, ([true,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 2 [true] [] [true] [false] 3 descLocal1 n (([true,true,true,true,true,false,true,true,true,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 26 ⟨2, ([true,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (27+3*n) ⟨4, ([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,true,false,true,true,true,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+3*n+26=27+3*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false,true]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,true,true,true,false])))) = (([false,true,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false,true,true,true,false])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 5 true) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((List.replicate 1 false)))))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((List.replicate 1 false)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false,true,true,true,false]
theorem desc (n : Nat) (R : List Bool) : run0 table (27+3*n) (atE 5 S (n+1) R) = some (atE 5 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 25 (atE 5 S 0 R) = some (atHead 5 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 5 S n (true::R)) = some (atHead 5 S (n+1) R) := by rfl

def family (n : Nat) := atE 5 S (n+0) []
def cost (n : Nat) := (costs 25 27 3 (n+0)).1

theorem entry : run0 table 41 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 5 S 25 27 3 base desc one (n+0)).1 []
  rw [show n+0+1=n+1+0 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+0 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 41 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M9402

namespace M10521

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem descStep0 (n : Nat) (R : List Bool) : run0 table 1 ⟨4, ([false]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,false]))), (R)⟩ = some ⟨5, (rep [true] n) ++ (([true,true,true,true,true,false,false])), ([true]) ++ ((R))⟩ := by rfl

theorem descLocal1 (L T : List Bool) : run0 table 1 ⟨5, ([true]) ++ ((L)), (T)⟩ = some ⟨5, (L), ([false]) ++ ((T))⟩ := by rfl

theorem descStep1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨5, (rep [true] n) ++ (([true,true,true,true,true,false,false])), ([true]) ++ ((R))⟩ = some ⟨5, ([true,true,true,true,true,false,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [] [] [true] [false] 1 descLocal1 n (([true,true,true,true,true,false,false])) (([true]) ++ ((R)))

theorem descStep2 (n : Nat) (R : List Bool) : run0 table 18 ⟨5, ([true,true,true,true,true,false,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([false,true,true,true,true,false,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by rfl

theorem descRaw (n : Nat) (R : List Bool) : run0 table (19+1*n) ⟨4, ([false]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,false]))), (R)⟩ = some ⟨4, ([false,true,true,true,true,false,false]), (rep [false] n) ++ (([true]) ++ ((R)))⟩ := by
  have H := descStep0 n R
  have H := join0 H (descStep1 n R)
  have H := join0 H (descStep2 n R)
  rw [show 1+1*n+18=19+1*n by omega] at H

  exact H

theorem descStart (n : Nat) : (([false]) ++ ((rep [true] n) ++ (([true,true,true,true,true,false,false])))) = (([false,true,true,true,true,true]) ++ ((rep [true] n) ++ (([false,false])))) := by
  change ((List.replicate 1 false) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 5 true) ++ ((List.replicate 2 false))))) = ((List.replicate 1 false) ++ ((List.replicate 5 true) ++ ((rep (List.replicate 1 true) n) ++ ((List.replicate 2 false)))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)


abbrev S : List Bool := [false,false]
theorem desc (n : Nat) (R : List Bool) : run0 table (19+1*n) (atE 4 S (n+1) R) = some (atE 4 S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using H

theorem base (R : List Bool) : run0 table 19 (atE 4 S 0 R) = some (atHead 4 S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead 4 S n (true::R)) = some (atHead 4 S (n+1) R) := by rfl

def family (n : Nat) := atE 4 S (n+1) []
def cost (n : Nat) := (costs 19 19 1 (n+1)).1

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table 4 S 19 19 1 base desc one (n+1)).1 []
  rw [show n+1+1=n+1+1 by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+1 <;> simp only [costs] <;> omega


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 cost entry positive growth m hm
#print axioms never

#print axioms growth
end M10521
end BB6.Agent11Raw121Counter
