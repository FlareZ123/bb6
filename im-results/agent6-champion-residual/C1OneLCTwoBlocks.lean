import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1TwoBlocks
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,21,11,24,14,10,3,16,12,11,7,9]
abbrev P : List Bool := [true,false]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev Z : List Bool := [false,false,false,false]
def u (n : Nat) : List Bool := List.replicate n true
theorem u_succ (n : Nat) : u (n+1) = true :: u n := rfl
theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,u_succ,u_succ,ih]; rfl

theorem e_one (L R : List Bool) :
    run0 ctr 3 ⟨4,h++L,f++R⟩ = some ⟨4,L,f++h++R⟩ := rfl

theorem e_sweep (n : Nat) (R : List Bool) :
    run0 ctr (3*n) ⟨4,u n,f++R⟩ = some ⟨4,[],f++u n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (e_one (u n) R) (ih (h++R))
    rw [show 3+3*n=3*(n+1) by omega] at H
    change run0 ctr (3*(n+1)) ⟨4,u (n+1),f++R⟩ = some ⟨4,[],f++u n++(u 1++R)⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) R,←u_add] at H
    exact H

theorem f_one (L R : List Bool) :
    run0 ctr 5 ⟨5,P++L,h++R⟩ = some ⟨5,P++h++L,R⟩ := rfl

theorem f_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (5*n) ⟨5,P++L,u n++R⟩ = some ⟨5,P++u n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f_one L (u n++R)) (ih (h++L))
    rw [show 5+5*n=5*(n+1) by omega] at H
    change run0 ctr (5*(n+1)) ⟨5,P++L,u (n+1)++R⟩ = some ⟨5,P++u n++(u 1++L),R⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) L,←u_add] at H
    exact H

theorem begin1 (L R : List Bool) :
    run0 ctr 15 ⟨5,P++h++L,Z++u 2++R⟩ = some ⟨4,L,f++Z++u 4++R⟩ := rfl

theorem turn (R : List Bool) :
    run0 ctr 11 ⟨4,[],f++u 3++R⟩ = some ⟨5,P++h,u 5++R⟩ := rfl

def cfg (m n : Nat) : Z0 := ⟨5,P++h,u m++Z++u n⟩
theorem cycle (m n : Nat) :
    run0 ctr (8*(m+3)+26) (cfg (m+3) (n+2)) = some (cfg (m+5) (n+4)) := by
  have H1 : run0 ctr (5*(m+3)) (cfg (m+3) (n+2)) = some ⟨5,P++u (m+4),Z++u (n+2)⟩ := by
    have H := f_sweep (m+3) h (Z++u (n+2))
    change run0 ctr (5*(m+3)) ⟨5,P++h,u (m+3)++(Z++u (n+2))⟩ = some ⟨5,P++u (m+3)++u 1,Z++u (n+2)⟩ at H
    rw [←List.append_assoc,List.append_assoc P,←u_add,show m+3+1=m+4 by omega] at H
    exact H
  have H2 : run0 ctr 15 ⟨5,P++u (m+4),Z++u (n+2)⟩ = some ⟨4,u (m+3),f++Z++u (n+4)⟩ := by
    have H := begin1 (u (m+3)) (u n)
    rw [List.append_assoc Z,←u_add,show 2+n=n+2 by omega, List.append_assoc (f++Z),←u_add,show 4+n=n+4 by omega] at H
    exact H
  have H3 : run0 ctr (3*(m+3)) ⟨4,u (m+3),f++Z++u (n+4)⟩ = some ⟨4,[],f++u (m+3)++Z++u (n+4)⟩ := by
    simpa only [List.append_assoc] using e_sweep (m+3) (Z++u (n+4))
  have H4 : run0 ctr 11 ⟨4,[],f++u (m+3)++Z++u (n+4)⟩ = some (cfg (m+5) (n+4)) := by
    have H := turn (u m++Z++u (n+4))
    simp only [List.append_assoc] at H ⊢
    rw [←List.append_assoc (u 3) (u m),←u_add,show 3+m=m+3 by omega,←List.append_assoc (u 5) (u m),←u_add,show 5+m=m+5 by omega] at H
    simpa only [cfg,List.append_assoc] using H
  have H := join0 (join0 (join0 H1 H2) H3) H4
  rwa [show 5*(m+3)+15+3*(m+3)+11=8*(m+3)+26 by omega] at H

theorem entry : run0 ctr 76 ⟨0,[],[]⟩ = some (cfg 6 2) := rfl

def family (k : Nat) : Z0 := cfg (6+2*k) (2+2*k)
theorem growth (k : Nat) : run0 ctr (8*(6+2*k)+26) (family k) = some (family (k+1)) := by
  unfold family
  have H := cycle (3+2*k) (2*k)
  rw [show 3+2*k+3=6+2*k by omega,show 2*k+2=2+2*k by omega,show 3+2*k+5=6+2*(k+1) by omega,show 2*k+4=2+2*(k+1) by omega] at H
  exact H

open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 76 (fun k => 8*(6+2*k)+26) entry
    (fun k => by omega) growth m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms cycle
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end BB6.Agent6C1TwoBlocks
