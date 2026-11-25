import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1Pair
open BB6Coverage BB6Coverage.Agent31Pump

def ctr (b : Bool) : PartialMachine := FAR.fromCodes [7,if b then 20 else 7,11,21,14,10,3,16,12,11,24,17]
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

def turnCost (b : Bool) : Nat := if b then 16 else 12
def pairCost (b : Bool) : Nat := if b then 12 else 8
def cturnCost (b : Bool) : Nat := if b then 8 else 4

theorem begin1 (b : Bool) (L : List Bool) :
    run0 (ctr b) 15 ⟨5,P++h++L,[]⟩ = some ⟨4,L,f++T⟩ := by cases b <;> rfl

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

theorem turn (b : Bool) (R : List Bool) :
    run0 (ctr b) (turnCost b) ⟨4,[],[false,true]++R⟩ = some ⟨5,P++u 2,u 2++R⟩ := by cases b <;> rfl

theorem f_pair (b : Bool) (L R : List Bool) :
    run0 (ctr b) (pairCost b) ⟨5,P++L,u 2++R⟩ = some ⟨5,P++u 2++L,R⟩ := by cases b <;> rfl

theorem f_sweep (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (ctr b) (pairCost b*n) ⟨5,P++L,u (2*n)++R⟩ = some ⟨5,P++u (2*n)++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f_pair b L (u (2*n)++R)) (ih (u 2++L))
    rw [Nat.mul_succ, Nat.add_comm (pairCost b*n)]
    rw [show 2*(n+1)=2*n+2 by omega,u_add]
    have eq : u (2*n) ++ u 2 = u 2 ++ u (2*n) := by rw [←u_add,←u_add,Nat.add_comm]
    rw [eq]
    simp only [List.append_assoc] at H
    rw [← List.append_assoc (u (2*n)) (u 2) L, eq, List.append_assoc] at H
    simpa only [List.append_assoc] using H

theorem begin2 (b : Bool) (L : List Bool) :
    run0 (ctr b) 11 ⟨5,P++h++L,T⟩ = some ⟨4,L,f++u 7⟩ := by cases b <;> rfl

theorem odd_turn (b : Bool) (L : List Bool) :
    run0 (ctr b) 8 ⟨5,P++L,h⟩ = some ⟨2,u 4++L,[]⟩ := by cases b <;> rfl

theorem c_one (b : Bool) (L R : List Bool) :
    run0 (ctr b) 1 ⟨2,h++L,R⟩ = some ⟨2,L,h++R⟩ := by cases b <;> rfl

theorem c_sweep (b : Bool) (n : Nat) (R : List Bool) :
    run0 (ctr b) n ⟨2,u n,R⟩ = some ⟨2,[],u n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (c_one b (u n) R) (ih (h++R))
    rw [show 1+n=n+1 by omega] at H
    change run0 (ctr b) (n+1) ⟨2,u (n+1),R⟩ = some ⟨2,[],u n++(u 1++R)⟩ at H
    rw [←List.append_assoc,←u_add] at H
    exact H

theorem c_turn (b : Bool) (R : List Bool) :
    run0 (ctr b) (cturnCost b) ⟨2,[],u 2++R⟩ = some ⟨5,P++u 2,R⟩ := by cases b <;> rfl

def cfg (m : Nat) : Z0 := ⟨5,P++u m,[]⟩
def cost (b : Bool) (n : Nat) : Nat := if b then 50*n+258 else 38*n+194

theorem cycle (b : Bool) (n : Nat) :
    run0 (ctr b) (cost b n) (cfg (2*n+2)) = some (cfg (2*n+16)) := by
  have H1 : run0 (ctr b) 15 (cfg (2*n+2)) = some ⟨4,u (2*n+1),f++T⟩ := begin1 b _
  have H2 := e_sweep b (2*n+1) T
  have H3 : run0 (ctr b) (turnCost b) ⟨4,[],f++u (2*n+1)++T⟩ = some ⟨5,P++u 2,u (2*n+2)++T⟩ := by
    have H := turn b (u (2*n)++T)
    rw [←List.append_assoc (u 2) (u (2*n)) T,←u_add,show 2+2*n=2*n+2 by omega] at H
    simpa only [List.append_assoc,u_succ,List.cons_append,List.nil_append] using H
  have H4 : run0 (ctr b) (pairCost b*(n+1)) ⟨5,P++u 2,u (2*n+2)++T⟩ = some ⟨5,P++u (2*n+4),T⟩ := by
    have H := f_sweep b (n+1) (u 2) T
    rw [List.append_assoc P,←u_add,show 2*(n+1)+2=2*n+4 by omega,show 2*(n+1)=2*n+2 by omega] at H
    exact H
  have H5 : run0 (ctr b) 11 ⟨5,P++u (2*n+4),T⟩ = some ⟨4,u (2*n+3),f++u 7⟩ := begin2 b _
  have H6 : run0 (ctr b) (3*(2*n+3)) ⟨4,u (2*n+3),f++u 7⟩ = some ⟨4,[],f++u (2*n+10)⟩ := by
    have H := e_sweep b (2*n+3) (u 7)
    rw [List.append_assoc,←u_add,show 2*n+3+7=2*n+10 by omega] at H
    exact H
  have H7 : run0 (ctr b) (turnCost b) ⟨4,[],f++u (2*n+10)⟩ = some ⟨5,P++u 2,u (2*n+11)⟩ := by
    have H := turn b (u (2*n+9))
    rw [←u_add,show 2+(2*n+9)=2*n+11 by omega] at H
    exact H
  have H8 : run0 (ctr b) (pairCost b*(n+5)) ⟨5,P++u 2,u (2*n+11)⟩ = some ⟨5,P++u (2*n+12),h⟩ := by
    have H := f_sweep b (n+5) (u 2) h
    change run0 (ctr b) (pairCost b*(n+5)) ⟨5,P++u 2,u (2*(n+5))++u 1⟩ = some ⟨5,P++u (2*(n+5))++u 2,h⟩ at H
    rw [←u_add,List.append_assoc P,←u_add,show 2*(n+5)+1=2*n+11 by omega,show 2*(n+5)+2=2*n+12 by omega] at H
    exact H
  have H9 : run0 (ctr b) 8 ⟨5,P++u (2*n+12),h⟩ = some ⟨2,u (2*n+16),[]⟩ := by
    have H := odd_turn b (u (2*n+12))
    rw [←u_add,show 4+(2*n+12)=2*n+16 by omega] at H
    exact H
  have H10 : run0 (ctr b) (2*n+16) ⟨2,u (2*n+16),[]⟩ = some ⟨2,[],u (2*n+16)⟩ := by
    simpa only [List.append_nil] using c_sweep b (2*n+16) []
  have H11 : run0 (ctr b) (cturnCost b) ⟨2,[],u (2*n+16)⟩ = some ⟨5,P++u 2,u (2*n+14)⟩ := by
    have H := c_turn b (u (2*n+14))
    rw [←u_add,show 2+(2*n+14)=2*n+16 by omega] at H
    exact H
  have H12 : run0 (ctr b) (pairCost b*(n+7)) ⟨5,P++u 2,u (2*n+14)⟩ = some (cfg (2*n+16)) := by
    have H := f_sweep b (n+7) (u 2) []
    rw [List.append_nil,List.append_assoc P,←u_add,show 2*(n+7)+2=2*n+16 by omega,show 2*(n+7)=2*n+14 by omega] at H
    exact H
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 H1 H2) H3) H4) H5) H6) H7) H8) H9) H10) H11) H12
  have hc : 15+3*(2*n+1)+turnCost b+pairCost b*(n+1)+11+3*(2*n+3)+turnCost b+pairCost b*(n+5)+8+(2*n+16)+cturnCost b+pairCost b*(n+7)=cost b n := by cases b <;> simp [turnCost,pairCost,cturnCost,cost] <;> omega
  rwa [hc] at H

def entryCost (b : Bool) : Nat := if b then 95 else 71
theorem entry (b : Bool) : run0 (ctr b) (entryCost b) ⟨0,[],[]⟩ = some (cfg 8) := by cases b <;> rfl

def family (k : Nat) : Z0 := cfg (8+14*k)
theorem growth (b : Bool) (k : Nat) : run0 (ctr b) (cost b (3+7*k)) (family k) = some (family (k+1)) := by
  unfold family
  rw [show 8+14*k=2*(3+7*k)+2 by omega,show 8+14*(k+1)=2*(3+7*k)+16 by omega]
  exact cycle b _

open BB6.Agent13BlankDelay
theorem never (b : Bool) (m : Machine) (hm : compatible (ctr b) m) : NeverHalts m :=
  never_of_growth (ctr b) family (entryCost b) (fun k => cost b (3+7*k)) (entry b)
    (fun k => by cases b <;> simp [cost] <;> omega) (growth b) m hm
theorem cover (b : Bool) (B : Nat) : Cover (WeightedBound B) (ctr b) :=
  .leaf _ (fun m hm => weighted_never B m (never b m hm))

#print axioms cycle
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end BB6.Agent6C1Pair
