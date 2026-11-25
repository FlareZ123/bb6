import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1Carry
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,21,11,24,14,10,3,16,12,11,9,3]
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [false,true,true]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
def u (n : Nat) : List Bool := List.replicate n true
def z (n : Nat) : List Bool := List.replicate n false
def ps (n : Nat) : List Bool := rep P n

theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change true :: u (a+b) = true :: (u a ++ u b); rw [ih]
theorem z_add (a b : Nat) : z (a+b) = z a ++ z b := by
  induction a with
  | zero => simp [z]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change false :: z (a+b) = false :: (z a ++ z b); rw [ih]
theorem ps_add (a b : Nat) : ps (a+b) = ps a ++ ps b := by
  induction a with
  | zero => simp [ps,rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change P ++ ps (a+b) = (P ++ ps a) ++ ps b; rw [ih,List.append_assoc]

-- All primitive moves are proved for arbitrary, unbounded tails.
theorem f0_zero (L R : List Bool) : run0 ctr 4 ⟨5,f++L,z 2++R⟩ = some ⟨5,f++P++L,R⟩ := rfl
theorem f0_one (L R : List Bool) : run0 ctr 5 ⟨5,f++P++L,h++R⟩ = some ⟨5,h++Q++L,R⟩ := rfl
theorem f1_pair (L R : List Bool) : run0 ctr 2 ⟨5,h++L,u 2++R⟩ = some ⟨5,h++P++L,R⟩ := rfl
theorem f1_end (L : List Bool) : run0 ctr 11 ⟨5,h++L,[]⟩ = some ⟨4,L,f++u 3⟩ := rfl
theorem f1_three (L R : List Bool) : run0 ctr 11 ⟨5,h++L,z 3++R⟩ = some ⟨4,L,f++u 3++R⟩ := rfl
theorem f1_two (L R : List Bool) : run0 ctr 9 ⟨5,h++Q++L,z 2++h++R⟩ = some ⟨4,h++L,f++u 5++R⟩ := rfl
theorem f1_eight (L R : List Bool) : run0 ctr 8 ⟨5,h++L,u 7++f++R⟩ = some ⟨5,f++ps 4++L,R⟩ := rfl
theorem popP (L R : List Bool) : run0 ctr 2 ⟨4,P++L,f++R⟩ = some ⟨4,L,f++z 2++R⟩ := rfl
theorem popQ (L R : List Bool) : run0 ctr 5 ⟨4,Q++L,f++R⟩ = some ⟨4,L,f++h++z 2++R⟩ := rfl
theorem popH (L R : List Bool) : run0 ctr 3 ⟨4,h++L,f++R⟩ = some ⟨4,L,f++h++R⟩ := rfl
theorem start (R : List Bool) : run0 ctr 6 ⟨5,h++P,u 5++f++R⟩ = some ⟨5,f++ps 4,R⟩ := rfl
theorem turn (R : List Bool) : run0 ctr 23 ⟨4,[],f++f++R⟩ = some ⟨5,h++P,u 5++R⟩ := rfl

theorem scan0 (n : Nat) (L R : List Bool) : run0 ctr (4*n) ⟨5,f++L,z (2*n)++R⟩ = some ⟨5,f++ps n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f0_zero L (z (2*n)++R)) (ih (P++L))
    rw [show 4+4*n=4*(n+1) by omega] at H
    have hz : z (2*(n+1)) = z 2 ++ z (2*n) := by rw [←z_add]; congr 1; omega
    have hp : ps (n+1) = ps n ++ P := by rw [←show ps 1=P by rfl,←ps_add]
    rw [hz,hp]
    simpa only [List.append_assoc] using H

theorem popn (n : Nat) (L R : List Bool) : run0 ctr (2*n) ⟨4,ps n++L,f++R⟩ = some ⟨4,L,f++z (2*n)++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (popP (ps n++L) R) (ih (z 2++R))
    rw [show 2+2*n=2*(n+1) by omega] at H
    have hz : z (2*(n+1)) = z (2*n) ++ z 2 := by rw [←z_add]; congr 1
    rw [hz]
    simpa only [ps,rep,List.append_assoc] using H

theorem consume (n : Nat) (L R : List Bool) : run0 ctr (8*n+5) ⟨5,f++P++L,z (4*n)++h++R⟩ = some ⟨5,h++Q++ps (2*n)++L,R⟩ := by
  have H := scan0 (2*n) (P++L) (h++R)
  have hp : ps (2*n)++P = P++ps (2*n) := by
    change ps (2*n)++ps 1 = ps 1++ps (2*n)
    rw [←ps_add,←ps_add,Nat.add_comm]
  have H' : run0 ctr (8*n) ⟨5,f++P++L,z (4*n)++h++R⟩ = some ⟨5,f++P++ps (2*n)++L,h++R⟩ := by
    rw [show 4*(2*n)=8*n by omega,show 2*(2*n)=4*n by omega] at H
    simp only [List.append_assoc] at H
    rw [←List.append_assoc (ps (2*n)) P L,hp] at H
    simpa only [List.append_assoc] using H
  simpa only [List.append_assoc] using join0 H' (f0_one (ps (2*n)++L) R)

inductive Tail : List Bool → Prop
  | end3 : Tail (u 3)
  | a (j : Nat) {R : List Bool} : Tail R → Tail (h++z (4*j+4)++R)
  | b (j : Nat) {R : List Bool} : Tail R → Tail (h++z 2++u 3++z (4*j+1)++R)
  | c (j : Nat) {R : List Bool} : Tail R → Tail (u 8++z (4*j+1)++R)

-- Scan through all leading c-blocks, execute the first a/b/end3,
-- then unwind the stack. Output remains in Tail, with the original zero prefix.
theorem transform {T : List Bool} (ht : Tail T) (n : Nat) (L : List Bool) :
    ∃ k U, 0<k ∧ Tail U ∧ run0 ctr k ⟨5,f++P++L,z (4*n)++T⟩ = some ⟨4,L,f++z (4*n)++U⟩ := by
  induction ht generalizing n L with
  | end3 =>
    have H1 : run0 ctr (8*n+5) ⟨5,f++P++L,z (4*n)++u 3⟩ = some ⟨5,h++Q++ps (2*n)++L,u 2⟩ := by rw [show u 3=h++u 2 by rfl]; simpa only [List.append_assoc] using consume n L (u 2)
    have H2 := f1_pair (Q++ps (2*n)++L) []
    have H3 := f1_end (P++Q++ps (2*n)++L)
    have H4 := popP (Q++ps (2*n)++L) (u 3)
    have H5 := popQ (ps (2*n)++L) (z 2++u 3)
    have H6 := popn (2*n) L (h++z 2++z 2++u 3)
    rw [show 2*(2*n)=4*n by omega] at H6
    have H := join0 H1 (by simpa only [List.append_assoc,List.append_nil] using H2)
    have H := join0 H (by simpa only [List.append_assoc] using H3)
    have H := join0 H (by simpa only [List.append_assoc] using H4)
    have H := join0 H (by simpa only [List.append_assoc] using H5)
    have H := join0 H (by simpa only [List.append_assoc] using H6)
    refine ⟨8*n+5+2+11+2+5+4*n,_,by omega,Tail.a 0 Tail.end3,?_⟩
    rw [show z (4*0+4)=z 2++z 2 by rfl]
    simpa only [List.append_assoc] using H
  | @a j R hr ih =>
    have H1 := consume n L (z (4*j+4)++R)
    have hz : z (4*j+4) = z 3 ++ z (4*j+1) := by rw [←z_add]; congr 1; omega
    have H2 := f1_three (Q++ps (2*n)++L) (z (4*j+1)++R)
    have H3 := popQ (ps (2*n)++L) (u 3++z (4*j+1)++R)
    have H4 := popn (2*n) L (h++z 2++u 3++z (4*j+1)++R)
    rw [show 2*(2*n)=4*n by omega] at H4
    rw [hz] at H1
    have H := join0 H1 (by simpa only [List.append_assoc] using H2)
    have H := join0 H (by simpa only [List.append_assoc] using H3)
    have H := join0 H (by simpa only [List.append_assoc] using H4)
    refine ⟨8*n+5+11+5+4*n,_,by omega,Tail.b j hr,?_⟩
    rw [hz]
    simpa only [List.append_assoc] using H
  | @b j R hr ih =>
    have H1 := consume n L (z 2++u 3++z (4*j+1)++R)
    have H2 := f1_two (ps (2*n)++L) (u 2++z (4*j+1)++R)
    have H3 := popH (ps (2*n)++L) (u 5++u 2++z (4*j+1)++R)
    have H4 := popn (2*n) L (h++u 5++u 2++z (4*j+1)++R)
    rw [show 2*(2*n)=4*n by omega] at H4
    rw [show u 3=h++u 2 by rfl] at H1
    have H := join0 H1 (by simpa only [List.append_assoc] using H2)
    have H := join0 H (by simpa only [List.append_assoc] using H3)
    have H := join0 H (by simpa only [List.append_assoc] using H4)
    refine ⟨8*n+5+9+3+4*n,_,by omega,Tail.c j hr,?_⟩
    rw [show u 3=h++u 2 by rfl,show u 8=h++u 5++u 2 by rfl]
    simpa only [List.append_assoc] using H
  | @c j R hr ih =>
    have H1 : run0 ctr (8*n+5) ⟨5,f++P++L,z (4*n)++(u 8++z (4*j+1)++R)⟩ = some ⟨5,h++Q++ps (2*n)++L,u 7++z (4*j+1)++R⟩ := by
      rw [show u 8=h++u 7 by rfl]
      simpa only [List.append_assoc] using consume n L (u 7++z (4*j+1)++R)
    have hz : z (4*j+1) = f++z (4*j) := by rw [←show z 1=f by rfl,←z_add]; congr 1; omega
    rw [hz] at H1
    have H2 := f1_eight (Q++ps (2*n)++L) (z (4*j)++R)
    obtain ⟨k,U,hk,hu,H3⟩ := ih j (ps 3++Q++ps (2*n)++L)
    have H4 := popn 3 (Q++ps (2*n)++L) (z (4*j)++U)
    have H5 := popQ (ps (2*n)++L) (z 6++z (4*j)++U)
    have H6 := popn (2*n) L (h++z (4*(j+1)+4)++U)
    rw [show 2*(2*n)=4*n by omega] at H6
    have he : z 2++z 6++z (4*j) = z (4*(j+1)+4) := by rw [←z_add,←z_add]; congr 1; omega
    have H := join0 H1 (by simpa only [List.append_assoc] using H2)
    rw [show ps 4=P++ps 3 by rfl] at H
    have H := join0 H (by simpa only [List.append_assoc] using H3)
    have H := join0 H (by simpa only [List.append_assoc] using H4)
    have H := join0 H (by simpa only [List.append_assoc] using H5)
    simp only [List.append_assoc] at H
    have he' : z 2++(z 6++(z (4*j)++U)) = z (4*(j+1)+4)++U := by rw [←List.append_assoc (z 6),←List.append_assoc (z 2),←List.append_assoc (z 2),he]
    rw [he'] at H
    have H := join0 H (by simpa only [List.append_assoc] using H6)
    refine ⟨8*n+5+8+k+2*3+5+4*n,_,by omega,Tail.a (j+1) hu,?_⟩
    rw [hz]
    simpa only [List.append_assoc] using H

def cfg (n : Nat) (R : List Bool) : Z0 := ⟨5,h++P,u 5++z (4*n+1)++R⟩

theorem advance {R : List Bool} (hr : Tail R) (n : Nat) :
    ∃ k U, 0<k ∧ Tail U ∧ run0 ctr k (cfg n R) = some (cfg (n+1) U) := by
  have hz : z (4*n+1) = f++z (4*n) := by rw [←show z 1=f by rfl,←z_add]; congr 1; omega
  have H1 : run0 ctr 6 (cfg n R) = some ⟨5,f++ps 4,z (4*n)++R⟩ := by
    unfold cfg
    rw [hz]
    simpa only [List.append_assoc] using start (z (4*n)++R)
  obtain ⟨k,U,hk,hu,H2⟩ := transform hr n (ps 3)
  have H3 := popn 3 [] (z (4*n)++U)
  have H4 := turn (z (4*n+5)++U)
  rw [show ps 4=P++ps 3 by rfl] at H1
  have H := join0 H1 (by simpa only [List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc,List.append_nil] using H3)
  have he : z 6++z (4*n) = f++z (4*n+5) := by rw [←show z 1=f by rfl,←z_add,←z_add]; congr 1; omega
  rw [←List.append_assoc (z (2*3)) (z (4*n)),show z (2*3)=z 6 by rfl,he] at H
  have H := join0 H (by simpa only [List.append_assoc] using H4)
  refine ⟨6+k+2*3+23,U,by omega,hu,?_⟩
  unfold cfg
  rw [show 4*(n+1)+1=4*n+5 by omega]
  simpa only [cfg,List.append_assoc] using H

theorem entry : run0 ctr 62 ⟨0,[],[]⟩ = some (cfg 1 (u 3)) := rfl

inductive Inv : Z0 → Prop
  | mk (n : Nat) {R : List Bool} : Tail R → Inv (cfg n R)

theorem progress {c : Z0} (hc : Inv c) : ∃ k c', 0<k ∧ run0 ctr k c = some c' ∧ Inv c' := by
  cases hc with
  | @mk n R hr =>
    obtain ⟨k,U,hk,hu,H⟩ := advance hr n
    exact ⟨k,cfg (n+1) U,hk,H,Inv.mk _ hu⟩

theorem next_exists (c : {c : Z0 // Inv c}) :
    ∃ p : Nat × {c : Z0 // Inv c}, 0<p.1 ∧ run0 ctr p.1 c.val = some p.2.val := by
  obtain ⟨k,t,hk,hr,ht⟩ := progress c.property
  exact ⟨(k,⟨t,ht⟩),hk,hr⟩
noncomputable def next (c : {c : Z0 // Inv c}) := Classical.choose (next_exists c)
theorem next_sound (c : {c : Z0 // Inv c}) :
    0<(next c).1 ∧ run0 ctr (next c).1 c.val = some (next c).2.val := Classical.choose_spec (next_exists c)
noncomputable def orbit : Nat → {c : Z0 // Inv c}
  | 0 => ⟨cfg 1 (u 3),Inv.mk 1 Tail.end3⟩
  | n+1 => (next (orbit n)).2

open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => (orbit k).val) 62 (fun k => (next (orbit k)).1) entry
    (fun k => (next_sound (orbit k)).1) (fun k => (next_sound (orbit k)).2) m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms transform
#print axioms advance
#print axioms entry
#print axioms next_sound
#print axioms never
#print axioms cover
end BB6.Agent6C1Carry
