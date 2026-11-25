import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1OneLC
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,2,11,21,14,10,3,16,12,11,24,3]
abbrev P : List Bool := [true,false]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev T : List Bool := [false,false,true,true,true]
def u (n : Nat) : List Bool := List.replicate n true

theorem u_succ (n : Nat) : u (n+1) = true :: u n := rfl
theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,u_succ,u_succ,ih]; rfl

theorem begin1 (L : List Bool) :
    run0 ctr 13 ⟨5,P++h++L,[]⟩ = some ⟨4,L,f++T⟩ := rfl

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

theorem turn (R : List Bool) :
    run0 ctr 14 ⟨4,[],[false,true]++R⟩ = some ⟨5,P++h,u 4++R⟩ := rfl

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

theorem begin2 (L : List Bool) :
    run0 ctr 9 ⟨5,P++h++L,T⟩ = some ⟨4,L,f++u 7⟩ := rfl

def cfg (n : Nat) : Z0 := ⟨5,P++u n,[]⟩

theorem cycle (n : Nat) : run0 ctr (16*n+155) (cfg (n+2)) = some (cfg (n+15)) := by
  have H1 : run0 ctr 13 (cfg (n+2)) = some ⟨4,u (n+1),f++T⟩ := by
    exact begin1 (u (n+1))
  have H2 := e_sweep (n+1) T
  have H3 : run0 ctr 14 ⟨4,[],f++u (n+1)++T⟩ = some ⟨5,P++h,u (n+4)++T⟩ := by
    have H := turn (u n++T)
    have e : u 4 ++ u n = u (n+4) := by rw [←u_add]; congr 1; omega
    rw [← List.append_assoc (u 4) (u n) T] at H
    rw [e] at H
    simpa only [List.append_assoc,u_succ,List.cons_append,List.nil_append] using H
  have H4 : run0 ctr (5*(n+4)) ⟨5,P++h,u (n+4)++T⟩ = some ⟨5,P++u (n+5),T⟩ := by
    have H := f_sweep (n+4) h T
    change run0 ctr (5*(n+4)) ⟨5,P++h,u (n+4)++T⟩ = some ⟨5,P++(u (n+4)++u 1),T⟩ at H
    rw [←u_add,show n+4+1=n+5 by omega] at H
    exact H
  have H5 : run0 ctr 9 ⟨5,P++u (n+5),T⟩ = some ⟨4,u (n+4),f++u 7⟩ := by
    exact begin2 (u (n+4))
  have H6 : run0 ctr (3*(n+4)) ⟨4,u (n+4),f++u 7⟩ = some ⟨4,[],f++u (n+11)⟩ := by
    have H := e_sweep (n+4) (u 7)
    rw [List.append_assoc,←u_add,show n+4+7=n+11 by omega] at H
    exact H
  have H7 : run0 ctr 14 ⟨4,[],f++u (n+11)⟩ = some ⟨5,P++h,u (n+14)⟩ := by
    have H := turn (u (n+10))
    rw [←u_add,show 4+(n+10)=n+14 by omega] at H
    have e : u (n+11) = true :: u (n+10) := by exact u_succ (n+10)
    rw [e]
    exact H
  have H8 : run0 ctr (5*(n+14)) ⟨5,P++h,u (n+14)⟩ = some (cfg (n+15)) := by
    unfold cfg
    have H := f_sweep (n+14) h []
    change run0 ctr (5*(n+14)) ⟨5,P++h,u (n+14)++[]⟩ = some ⟨5,P++(u (n+14)++u 1),[]⟩ at H
    rw [←u_add,show n+14+1=n+15 by omega] at H
    simpa only [List.append_nil] using H
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 H1 H2) H3) H4) H5) H6) H7) H8
  rw [show 13+3*(n+1)+14+5*(n+4)+9+3*(n+4)+14+5*(n+14)=16*n+155 by omega] at H
  exact H

theorem entry : run0 ctr 46 ⟨0,[],[]⟩ = some (cfg 6) := rfl

def family (k : Nat) : Z0 := cfg (6+13*k)
theorem growth (k : Nat) : run0 ctr (16*(4+13*k)+155) (family k) = some (family (k+1)) := by
  unfold family
  rw [show 6+13*k=(4+13*k)+2 by omega,show 6+13*(k+1)=(4+13*k)+15 by omega]
  exact cycle _

open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 46 (fun k => 16*(4+13*k)+155) entry
    (fun k => by omega) growth m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms cycle
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end BB6.Agent6C1OneLC
