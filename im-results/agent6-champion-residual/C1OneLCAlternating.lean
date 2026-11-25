import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1Alternating
open BB6Coverage BB6Coverage.Agent31Pump

def ctr (b : Bool) : PartialMachine := if b then FAR.fromCodes [7,22,11,24,14,10,3,16,12,11,23,1] else FAR.fromCodes [7,21,11,24,14,10,3,16,12,11,7,14]
def P (b : Bool) : List Bool := if b then [] else [true,false]
def d (b : Bool) : Nat := if b then 2 else 0
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev T : List Bool := [false,false,true,true]
def u (n : Nat) : List Bool := List.replicate n true
theorem u_succ (n : Nat) : u (n+1) = true :: u n := rfl
theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,u_succ,u_succ,ih]; rfl

theorem e_one (b : Bool) (L R : List Bool) :
    run0 (ctr b) 3 ⟨4,h++L,f++R⟩ = some ⟨4,L,f++h++R⟩ := by cases b <;> rfl

theorem e_sweep (b : Bool) (n : Nat) (R : List Bool) :
    run0 (ctr b) (3*n) ⟨4,u n,f++R⟩ = some ⟨4,[],f++u n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (e_one b (u n) R) (ih (h++R))
    rw [show 3+3*n=3*(n+1) by omega] at H
    change run0 (ctr b) (3*(n+1)) ⟨4,u (n+1),f++R⟩ = some ⟨4,[],f++u n++(u 1++R)⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) R,←u_add] at H
    exact H

theorem f_one (b : Bool) (L R : List Bool) :
    run0 (ctr b) 3 ⟨5,(P b++h)++L,h++R⟩ = some ⟨5,(P b++h)++(h++L),R⟩ := by cases b <;> rfl

theorem f_sweep (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (ctr b) (3*n) ⟨5,(P b++h)++L,u n++R⟩ = some ⟨5,(P b++h)++(u n++L),R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f_one b L (u n++R)) (ih (h++L))
    rw [show 3+3*n=3*(n+1) by omega] at H
    change run0 (ctr b) (3*(n+1)) ⟨5,(P b++h)++L,u (n+1)++R⟩ = some ⟨5,(P b++h)++(u n++(u 1++L)),R⟩ at H
    rw [← List.append_assoc (u n) (u 1) L,←u_add] at H
    exact H

theorem begin1 (b : Bool) (L : List Bool) :
    run0 (ctr b) (12-d b) ⟨5,P b++u (1+d b)++L,[]⟩ = some ⟨4,h++L,f++T⟩ := by cases b <;> rfl

theorem begin2 (b : Bool) (L : List Bool) :
    run0 (ctr b) (10-d b) ⟨5,P b++u (1+d b)++L,T⟩ = some ⟨4,h++L,f++u 5⟩ := by cases b <;> rfl

theorem turn (b : Bool) (R : List Bool) :
    run0 (ctr b) 11 ⟨4,[],f++u 3++R⟩ = some ⟨5,P b++h,u (5+d b)++R⟩ := by cases b <;> rfl

def cfg (b : Bool) (w : Nat) : Z0 := ⟨5,P b++h,u (w+d b)⟩
def cfg2 (b : Bool) (w : Nat) : Z0 := ⟨5,P b++h,u (w+d b)++T⟩

theorem shape (b : Bool) (w : Nat) : (P b++h)++u (w+d b) = P b++u (1+d b)++u w := by
  change (P b++u 1)++u (w+d b) = P b++u (1+d b)++u w
  rw [List.append_assoc,←u_add,List.append_assoc,←u_add]
  congr 2
  omega

theorem phase1 (b : Bool) (w : Nat) :
    run0 (ctr b) (6*(w+2)+26+2*d b) (cfg b (w+2)) = some (cfg2 b (w+5)) := by
  have H1 : run0 (ctr b) (3*(w+2+d b)) (cfg b (w+2)) = some ⟨5,P b++u (1+d b)++u (w+2),[]⟩ := by
    have H := f_sweep b (w+2+d b) [] []
    simp only [List.append_nil] at H
    rw [shape] at H
    exact H
  have H2 := begin1 b (u (w+2))
  have H3 : run0 (ctr b) (3*(w+3)) ⟨4,h++u (w+2),f++T⟩ = some ⟨4,[],f++u (w+3)++T⟩ := e_sweep b (w+3) T
  have H4 : run0 (ctr b) 11 ⟨4,[],f++u (w+3)++T⟩ = some (cfg2 b (w+5)) := by
    have H := turn b (u w++T)
    simp only [cfg2,List.append_assoc] at H ⊢
    rw [←List.append_assoc (u 3) (u w),←u_add,show 3+w=w+3 by omega,←List.append_assoc (u (5+d b)) (u w),←u_add,show 5+d b+w=w+5+d b by omega] at H
    exact H
  have H := join0 (join0 (join0 H1 H2) H3) H4
  have e : 3*(w+2+d b)+(12-d b)+3*(w+3)+11=6*(w+2)+26+2*d b := by cases b <;> simp [d] <;> omega
  rw [e] at H
  exact H

theorem phase2 (b : Bool) (w : Nat) :
    run0 (ctr b) (6*w+24+2*d b) (cfg2 b w) = some (cfg b (w+8)) := by
  have H1 : run0 (ctr b) (3*(w+d b)) (cfg2 b w) = some ⟨5,P b++u (1+d b)++u w,T⟩ := by
    have H := f_sweep b (w+d b) [] T
    simp only [List.append_nil] at H
    rw [shape] at H
    exact H
  have H2 := begin2 b (u w)
  have H3 : run0 (ctr b) (3*(w+1)) ⟨4,h++u w,f++u 5⟩ = some ⟨4,[],f++u (w+6)⟩ := by
    have H := e_sweep b (w+1) (u 5)
    rw [List.append_assoc,←u_add,show w+1+5=w+6 by omega] at H
    exact H
  have H4 : run0 (ctr b) 11 ⟨4,[],f++u (w+6)⟩ = some (cfg b (w+8)) := by
    have H := turn b (u (w+3))
    rw [List.append_assoc f,←u_add,←u_add,show 3+(w+3)=w+6 by omega,show 5+d b+(w+3)=w+8+d b by omega] at H
    exact H
  have H := join0 (join0 (join0 H1 H2) H3) H4
  have e : 3*(w+d b)+(10-d b)+3*(w+1)+11=6*w+24+2*d b := by cases b <;> simp [d] <;> omega
  rwa [e] at H

theorem cycle (b : Bool) (w : Nat) : run0 (ctr b) (12*(w+2)+68+4*d b) (cfg b (w+2)) = some (cfg b (w+13)) := by
  have H := join0 (phase1 b w) (phase2 b (w+5))
  rwa [show 6*(w+2)+26+2*d b+(6*(w+5)+24+2*d b)=12*(w+2)+68+4*d b by omega] at H

theorem entry (b : Bool) : run0 (ctr b) 18 ⟨0,[],[]⟩ = some (cfg b 4) := by cases b <;> rfl

def family (b : Bool) (k : Nat) : Z0 := cfg b (4+11*k)
theorem growth (b : Bool) (k : Nat) : run0 (ctr b) (12*(4+11*k)+68+4*d b) (family b k) = some (family b (k+1)) := by
  unfold family
  have H := cycle b (2+11*k)
  rw [show 2+11*k+2=4+11*k by omega,show 2+11*k+13=4+11*(k+1) by omega] at H
  exact H

open BB6.Agent13BlankDelay
theorem never (b : Bool) (m : Machine) (hm : compatible (ctr b) m) : NeverHalts m :=
  never_of_growth (ctr b) (family b) 18 (fun k => 12*(4+11*k)+68+4*d b) (entry b)
    (fun k => by omega) (growth b) m hm
theorem cover (b : Bool) (B : Nat) : Cover (WeightedBound B) (ctr b) :=
  .leaf _ (fun m hm => weighted_never B m (never b m hm))

#print axioms cycle
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end BB6.Agent6C1Alternating
