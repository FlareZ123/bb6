import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1Triple
open BB6Coverage BB6Coverage.Agent31Pump
inductive Variant | zero | one | two
open Variant
def i : Variant → Nat | zero => 0 | one => 1 | two => 2
def code : Variant → Nat | zero => 5 | one => 1 | two => 13
def ctr (v : Variant) : PartialMachine := FAR.fromCodes [7,21,11,24,14,10,3,16,12,11,code v,9]
abbrev P : List Bool := [true,false]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
def u (n : Nat) : List Bool := List.replicate n true
theorem u_succ (n : Nat) : u (n+1) = true :: u n := rfl
theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,u_succ,u_succ,ih]; rfl

theorem begin1 (v : Variant) (L : List Bool) :
    run0 (ctr v) (19+4*i v) ⟨5,P++h++L,[]⟩ = some ⟨4,L,f++u (6+i v)⟩ := by cases v <;> rfl

theorem e_one (v : Variant) (L R : List Bool) :
    run0 (ctr v) 3 ⟨4,h++L,f++R⟩ = some ⟨4,L,f++h++R⟩ := by cases v <;> rfl

theorem e_sweep (v : Variant) (n : Nat) (R : List Bool) :
    run0 (ctr v) (3*n) ⟨4,u n,f++R⟩ = some ⟨4,[],f++u n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (e_one v (u n) R) (ih (h++R))
    rw [show 3+3*n=3*(n+1) by omega] at H
    change run0 (ctr v) (3*(n+1)) ⟨4,u (n+1),f++R⟩ = some ⟨4,[],f++u n++(u 1++R)⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) R,←u_add] at H
    exact H

theorem f_one (v : Variant) (L R : List Bool) :
    run0 (ctr v) 5 ⟨5,P++L,h++R⟩ = some ⟨5,P++h++L,R⟩ := by cases v <;> rfl

theorem f_sweep (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (ctr v) (5*n) ⟨5,P++L,u n++R⟩ = some ⟨5,P++u n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f_one v L (u n++R)) (ih (h++L))
    rw [show 5+5*n=5*(n+1) by omega] at H
    change run0 (ctr v) (5*(n+1)) ⟨5,P++L,u (n+1)++R⟩ = some ⟨5,P++u n++(u 1++L),R⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) L,←u_add] at H
    exact H

theorem turn (v : Variant) (R : List Bool) :
    run0 (ctr v) 11 ⟨4,[],f++u 3++R⟩ = some ⟨5,P++h,u 5++R⟩ := by cases v <;> rfl

def cfg (m : Nat) : Z0 := ⟨5,P++u m,[]⟩
theorem cycle (v : Variant) (n : Nat) :
    run0 (ctr v) (8*n+70+9*i v) (cfg (n+1)) = some (cfg (n+9+i v)) := by
  have H1 : run0 (ctr v) (19+4*i v) (cfg (n+1)) = some ⟨4,u n,f++u (6+i v)⟩ := begin1 v _
  have H2 : run0 (ctr v) (3*n) ⟨4,u n,f++u (6+i v)⟩ = some ⟨4,[],f++u (n+6+i v)⟩ := by
    have H := e_sweep v n (u (6+i v))
    rw [List.append_assoc,←u_add,show n+(6+i v)=n+6+i v by omega] at H
    exact H
  have H3 : run0 (ctr v) 11 ⟨4,[],f++u (n+6+i v)⟩ = some ⟨5,P++h,u (n+8+i v)⟩ := by
    have H := turn v (u (n+3+i v))
    rw [List.append_assoc f,←u_add,←u_add,show 3+(n+3+i v)=n+6+i v by omega,show 5+(n+3+i v)=n+8+i v by omega] at H
    exact H
  have H4 : run0 (ctr v) (5*(n+8+i v)) ⟨5,P++h,u (n+8+i v)⟩ = some (cfg (n+9+i v)) := by
    have H := f_sweep v (n+8+i v) h []
    change run0 (ctr v) (5*(n+8+i v)) ⟨5,P++h,u (n+8+i v)++[]⟩ = some ⟨5,P++u (n+8+i v)++u 1,[]⟩ at H
    rw [List.append_nil,List.append_assoc P,←u_add,show n+8+i v+1=n+9+i v by omega] at H
    exact H
  have H := join0 (join0 (join0 H1 H2) H3) H4
  rwa [show 19+4*i v+3*n+11+5*(n+8+i v)=8*n+70+9*i v by omega] at H

theorem entry (v : Variant) : run0 (ctr v) 38 ⟨0,[],[]⟩ = some (cfg 5) := by cases v <;> rfl

def family (v : Variant) (k : Nat) : Z0 := cfg (5+(8+i v)*k)
theorem growth (v : Variant) (k : Nat) :
    run0 (ctr v) (8*(4+(8+i v)*k)+70+9*i v) (family v k) = some (family v (k+1)) := by
  unfold family
  have e1 : 5+(8+i v)*k=(4+(8+i v)*k)+1 := by omega
  have e2 : 5+(8+i v)*(k+1)=(4+(8+i v)*k)+9+i v := by rw [Nat.mul_succ]; omega
  rw [e1,e2]
  exact cycle v _

open BB6.Agent13BlankDelay
theorem never (v : Variant) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m :=
  never_of_growth (ctr v) (family v) 38 (fun k => 8*(4+(8+i v)*k)+70+9*i v) (entry v)
    (fun k => by omega) (growth v) m hm
theorem cover (v : Variant) (B : Nat) : Cover (WeightedBound B) (ctr v) :=
  .leaf _ (fun m hm => weighted_never B m (never v m hm))

#print axioms cycle
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end BB6.Agent6C1Triple
