import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCounter99
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def Z : List Bool := [false,false]
def O : List Bool := [true,true]
def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => b::false::enc bs
def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs
def carries : List Bool → Nat
  | [] => 1
  | false::_ => 0
  | true::bs => carries bs + 1
def cfg (n : Nat) (bs : List Bool) : Z0 := ⟨0,false::false::enc bs,false::rep O (n+1)⟩

theorem zero_rotate (n : Nat) (p : List Bool) :
    rep Z n ++ false::p = false::(rep Z n ++ p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::false::(rep Z n ++ false::p) = false::false::false::(rep Z n ++ p)
    rw [ih]

theorem prepare (n : Nat) (bs : List Bool) :
    run0 table (4*n+12) (cfg n bs) =
      some ⟨5,enc bs,true::false::false::rep O (n+2)⟩ := by
  have a : run0 table 3 (cfg n bs) = some ⟨0,[true,false,true,true,false]++enc bs,rep O n⟩ := by rfl
  have b := sweepR table 0 [true] [] O Z 2 (by intro L R; rfl) n ([false,true,true,false]++enc bs) []
  simp only [List.nil_append,List.append_nil,List.cons_append] at b
  have c : run0 table 2 ⟨0,true::(rep Z n ++ [false,true,true,false]++enc bs),[]⟩ =
      some ⟨3,[false,false,false]++(rep Z n ++ [false,true,true,false]++enc bs),[]⟩ := by rfl
  have E : [false,false,false]++(rep Z n ++ [false,true,true,false]++enc bs) =
      rep Z (n+2) ++ ([true,true,false]++enc bs) := by
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [zero_rotate]
    rfl
  rw [E] at c
  simp only [List.append_assoc,List.cons_append,List.nil_append] at c
  have d := sweepL table 3 [] [] Z O 2 (by intro L R; rfl) (n+2) ([true,true,false]++enc bs) []
  simp only [List.nil_append,List.append_nil] at d
  have e : run0 table 3 ⟨3,[true,true,false]++enc bs,rep O (n+2)⟩ =
      some ⟨5,enc bs,true::false::false::rep O (n+2)⟩ := by rfl
  have H := join0 (join0 (join0 (join0 a b) c) d) e
  rw [show 3+2*n+2+2*(n+2)+3=4*n+12 by omega] at H
  exact H

theorem restore (k : Nat) (l T : List Bool) (hl : l.headD false = false) :
    run0 table (2*k+2) ⟨5,l,rep O k ++ true::false::false::T⟩ =
      some ⟨0,false::false::(rep Z k ++ true::l.tail),false::T⟩ := by
  cases k with
  | zero =>
    cases l with
    | nil => rfl
    | cons b l => cases b <;> simp_all [rep] <;> rfl
  | succ k =>
    have a : run0 table 2 ⟨5,l,rep O (k+1) ++ true::false::false::T⟩ =
        some ⟨0,true::false::true::l.tail,rep O k ++ true::false::false::T⟩ := by
      cases l with
      | nil => rfl
      | cons b l => cases b <;> simp_all [rep] <;> rfl
    have b := sweepR table 0 [true] [] O Z 2 (by intro L R; rfl) k (false::true::l.tail) (true::false::false::T)
    simp only [List.nil_append,List.cons_append] at b
    have c : run0 table 2 ⟨0,true::(rep Z k ++ false::true::l.tail),true::false::false::T⟩ =
        some ⟨0,false::false::false::(rep Z k ++ false::true::l.tail),false::T⟩ := by rfl
    have H := join0 (join0 a b) c
    rw [zero_rotate] at H
    rw [show 2+2*k+2=2*(k+1)+2 by omega] at H
    simpa only [rep,Z,List.cons_append,List.nil_append] using H

theorem scan (bs : List Bool) (k : Nat) (T : List Bool) :
    run0 table (2*k+4*carries bs+2) ⟨5,enc bs,rep O k ++ true::false::false::T⟩ =
      some ⟨0,false::false::(rep Z k ++ enc (bump bs)),false::T⟩ := by
  induction bs generalizing k with
  | nil =>
    have a : run0 table 2 ⟨5,enc [],rep O k ++ true::false::false::T⟩ =
        some ⟨5,[],rep O (k+1) ++ true::false::false::T⟩ := by rfl
    have b := restore (k+1) [] T (by rfl)
    have H := join0 a b
    rw [show 2+(2*(k+1)+2)=2*k+4*carries []+2 by simp [carries]; omega] at H
    have eq : rep Z (k+1) ++ [true] = rep Z k ++ enc (bump []) := by
      rw [rep,← rep_snoc]
      simp only [bump,enc,List.append_assoc,Z,List.cons_append,List.nil_append]
    change run0 table _ _ = some ⟨0,false::false::(rep Z (k+1) ++ [true]),false::T⟩ at H
    rw [eq] at H
    exact H
  | cons b bs ih =>
    cases b with
    | false =>
      have H := restore k (enc (false::bs)) T (by rfl)
      simpa [enc,bump,carries] using H
    | true =>
      have a : run0 table 2 ⟨5,enc (true::bs),rep O k ++ true::false::false::T⟩ =
          some ⟨5,enc bs,rep O (k+1) ++ true::false::false::T⟩ := by rfl
      have H := join0 a (ih (k+1))
      rw [show 2+(2*(k+1)+4*carries bs+2)=2*k+4*carries (true::bs)+2 by simp [carries]; omega] at H
      have eq : rep Z (k+1) ++ enc (bump bs) = rep Z k ++ enc (bump (true::bs)) := by
        rw [rep,← rep_snoc]
        simp only [bump,enc,List.append_assoc,Z,List.cons_append,List.nil_append]
      rw [eq] at H
      exact H

theorem epoch (n : Nat) (bs : List Bool) :
    run0 table (4*n+14+4*carries bs) (cfg n bs) = some (cfg (n+1) (bump bs)) := by
  have H := join0 (prepare n bs) (scan bs 0 (rep O (n+2)))
  rw [show 4*n+12+(2*0+4*carries bs+2)=4*n+14+4*carries bs by omega] at H
  exact H

def orbit : Nat → List Bool | 0 => [] | n+1 => bump (orbit n)
def family (n : Nat) : Z0 := cfg n (orbit n)
theorem first : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (4*n+14+4*carries (orbit n)) (family n) = some (family (n+1)) := epoch n (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 4*n+14+4*carries (orbit n)) first (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFCounter99
