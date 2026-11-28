import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7D100UnaryDouble
open BB6Coverage BB6Coverage.Agent31Pump

/-- Original Raw36 D1=0LA one-hole literal; E0 is the only missing row.
    1RB1LA_1RC1LE_0RD0LB_0LD0LA_---0LF_1LC0RA -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨false,false,0⟩)
  | 4,true  => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

def pair : List Bool := [true,true]
def alt : List Bool := [true,false,true,false]
def quad : List Bool := [true,true,true,true]

theorem rep_quad (j : Nat) : rep quad j = rep pair (2*j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1) = 2*j+2 by omega]
    simp only [rep]
    rw [ih]
    rfl

theorem pair_true (j : Nat) : rep pair j ++ [true] = true :: rep pair j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    rfl

theorem right_first (R : List Bool) :
    run0 table 8 ⟨2,[],alt++R⟩ = some ⟨2,[false]++quad,R⟩ := by rfl

theorem right_one (L R : List Bool) :
    run0 table 8 ⟨2,[false]++L,alt++R⟩ =
    some ⟨2,[false]++quad++L,R⟩ := by rfl

theorem right_all (j : Nat) (R : List Bool) :
    run0 table (8*(j+1)) ⟨2,[],rep alt (j+1)++R⟩ =
    some ⟨2,[false]++rep quad (j+1),R⟩ := by
  have h := right_first (rep alt j++R)
  have g := sweepR table 2 [false] [] alt quad 8 right_one j quad R
  have H := join0 h (by simpa only [List.nil_append] using g)
  rw [show 8*(j+1) = 8+8*j by omega]
  simpa only [rep,List.append_assoc,rep_snoc,List.nil_append] using H

theorem turn (L R : List Bool) :
    run0 table 4 ⟨2,false::L,true::true::R⟩ = some ⟨2,[true,true,true]++L,R⟩ := by rfl

theorem left_one (L R : List Bool) :
    run0 table 8 ⟨2,[true,true,true]++quad++L,R⟩ =
    some ⟨2,[true,true,true]++L,alt++R⟩ := by rfl

theorem left_last (R : List Bool) :
    run0 table 4 ⟨2,[true,true,true],R⟩ = some ⟨2,[],alt++R⟩ := by rfl

theorem consume (j : Nat) (R : List Bool) :
    run0 table (16*(j+1)+8) ⟨2,[],rep alt (j+1)++true::true::R⟩ =
    some ⟨2,[],rep alt (j+2)++R⟩ := by
  have h := right_all j (true::true::R)
  have g := turn (rep quad (j+1)) R
  have hg := join0 h g
  have k := sweepL table 2 [true,true,true] [] quad alt 8 left_one (j+1) [] R
  have hgk := join0 hg (by simpa only [List.append_nil,List.nil_append] using k)
  have H := join0 hgk (left_last (rep alt (j+1)++R))
  rw [show 16*(j+1)+8 = 8*(j+1)+4+8*(j+1)+4 by omega]
  simpa only [rep,List.append_assoc,List.nil_append,List.append_nil] using H

theorem terminal_turn (L R : List Bool) :
    run0 table 8 ⟨2,false::L,true::false::false::R⟩ =
    some ⟨0,true::L,false::false::false::R⟩ := by rfl

theorem A_first (L R : List Bool) :
    run0 table 1 ⟨0,true::L,R⟩ = some ⟨0,L,true::R⟩ := by rfl

theorem A_quad (L R : List Bool) :
    run0 table 4 ⟨0,quad++L,R⟩ = some ⟨0,L,quad++R⟩ := by rfl

theorem finish (j : Nat) (R : List Bool) :
    run0 table (12*(j+1)+9) ⟨2,[],rep alt (j+1)++true::false::false::R⟩ =
    some ⟨0,[],true::rep pair (2*(j+1))++false::false::false::R⟩ := by
  have h := right_all j (true::false::false::R)
  have g := terminal_turn (rep quad (j+1)) R
  have hg := join0 h g
  have hga := join0 hg (A_first (rep quad (j+1)) (false::false::false::R))
  have k := sweepL table 0 [] [] quad quad 4 A_quad (j+1) [] (true::false::false::false::R)
  have H := join0 hga (by simpa only [List.nil_append,List.append_nil] using k)
  rw [show 12*(j+1)+9 = 8*(j+1)+8+1+4*(j+1) by omega]
  simp only [rep_quad] at H
  have hp := congrArg (fun x : List Bool => x ++ false::false::false::R) (pair_true (2*(j+1)))
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hp
  rw [hp] at H
  exact H

def A (m z : Nat) : Z0 := ⟨0,[],true::rep pair (m+2)++false::false::rep [false] z⟩
def C (j m z : Nat) : Z0 := ⟨2,[],rep alt (j+1)++true::rep pair m++false::false::rep [false] z⟩

theorem start (R : List Bool) :
    run0 table 50 ⟨0,[],[true,true,true,true,true]++R⟩ =
    some ⟨2,[],rep alt 2++true::R⟩ := by rfl

theorem start_phase (m z : Nat) : run0 table 50 (A m z) = some (C 1 m z) := by
  simpa only [A,C,rep,pair,List.append_assoc,List.cons_append,List.nil_append] using
    start (rep pair m++false::false::rep [false] z)

theorem consume_phase (j m z : Nat) :
    run0 table (16*(j+1)+8) (C j (m+1) z) = some (C (j+1) m z) := by
  simpa only [C,rep,pair,List.append_assoc,List.cons_append,List.nil_append] using
    consume j (true::rep pair m++false::false::rep [false] z)

theorem finish_phase (j z : Nat) :
    run0 table (12*(j+1)+9) (C j 0 z) = some (A (2*j) (z+1)) := by
  have h := finish j (rep [false] z)
  rw [show 2*(j+1) = 2*j+2 by omega] at h
  simpa only [A,C,rep,List.nil_append,List.cons_append,List.append_assoc] using h

def closeCost (j : Nat) : Nat → Nat
  | 0 => 12*(j+1)+9
  | m+1 => (16*(j+1)+8)+closeCost (j+1) m

theorem close (j m z : Nat) :
    run0 table (closeCost j m) (C j m z) = some (A (2*(j+m)) (z+1)) := by
  induction m generalizing j with
  | zero => simpa only [closeCost,Nat.add_zero] using finish_phase j z
  | succ m ih =>
    have h := join0 (consume_phase j m z) (ih (j+1))
    rw [show j+1+m=j+(m+1) by omega] at h
    exact h

def param : Nat → Nat
  | 0 => 3
  | k+1 => 2*param k+2

def family (k : Nat) : Z0 := A (param k) (5+k)
def cost (k : Nat) : Nat := 50+closeCost 1 (param k)

theorem entry : run0 table 199 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h := join0 (start_phase (param k) (5+k)) (close 1 (param k) (5+k))
  rw [show 2*(1+param k)=2*param k+2 by omega] at h
  simpa only [cost,family,param,Nat.add_assoc] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 199 cost entry (by intro k; unfold cost; omega) growth m hm

#print axioms entry
#print axioms growth
#print axioms never
end BB6.Agent7D100UnaryDouble
