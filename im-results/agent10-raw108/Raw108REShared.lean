import SweepPumping
namespace BB6.Agent10Raw108REShared
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨v,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,if v then 4 else 0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨!v,false,0⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev ones (n : Nat) := List.replicate n true
def P (v : Bool) : List Bool := [!v,v]
def bc (v : Bool) := if v then 12 else 6

theorem commute (W : List Bool) (k : Nat) (R : List Bool) : rep W k ++ (W++R) = W ++ (rep W k++R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (W++rep W k)++(W++R) = W++((W++rep W k)++R)
    simp only [List.append_assoc,ih]

theorem out_one (v : Bool) (L R : List Bool) : run0 (table v) 2 (A (true::true::L) R) = some (A L (P v++R)) := by cases v <;> rfl

theorem out_all (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) (2*k) (A (ones (2*k)) R) = some (A [] (rep (P v) k++R)) := by
  induction k generalizing R with
  | zero => simp [run0,rep]
  | succ k ih =>
    have h := join0 (out_one v (ones (2*k)) R) (ih (P v++R))
    rw [commute] at h
    rw [show 2+2*k=2*(k+1) by omega] at h
    have e : 2*(k+1)=2*k+2 := by omega
    rw [e]
    rw [e] at h
    exact h

theorem back_last (v : Bool) (L : List Bool) :
    run0 (table v) (bc v) (A (false::L) (P v++P v)) = some (A (false::true::true::true::true::L) (if v then [false] else [])) := by cases v <;> rfl

theorem reset (v : Bool) (L : List Bool) : run0 (table v) 11 (A (false::true::true::L) (if v then [false] else [])) = some (A (true::true::true::true::true::true::L) []) := by cases v <;> rfl

def D (v : Bool) := P v++P v

theorem pair_rep (v : Bool) (k : Nat) : rep (P v) (2*k) = rep (D v) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega]
    simp only [rep,List.append_assoc,D,ih]

theorem back_more (v : Bool) (L R : List Bool) :
    run0 (table v) (bc v) (A (false::L) (D v++D v++R)) = some (A (false::true::true::true::true::L) (D v++R)) := by cases v <;> rfl

theorem back_all (v : Bool) (k l : Nat) : run0 (table v) (bc v*(k+1)) (A (false::ones l) (rep (D v) (k+1))) = some (A (false::ones (4*(k+1)+l)) (if v then [false] else [])) := by
  induction k generalizing l with
  | zero =>
    have h := back_last v (ones l)
    rw [show 4*(0+1)+l=l+4 by omega]
    simp only [Nat.zero_add,Nat.mul_one,rep,List.append_nil,D]
    change run0 (table v) (bc v) (A (false::ones l) (P v++P v)) = some (A (false::true::true::true::true::ones l) (if v then [false] else []))
    exact h
  | succ k ih =>
    have h := join0 (back_more v (ones l) (rep (D v) k)) (ih (l+4))
    rw [show bc v*(k+1+1)=bc v+bc v*(k+1) by rw [Nat.mul_succ,Nat.add_comm],show 4*(k+1+1)+l=4*(k+1)+(l+4) by omega]
    simpa only [rep,List.append_assoc] using h

theorem pad (v : Bool) (t : Nat) (R : List Bool) : run0 (table v) (t+1) (A [] R) = run0 (table v) (t+1) (A [false] R) := by rfl

def family (n : Nat) := A (ones (4*n+4)) []
def cost (v : Bool) (n : Nat) := 2*(2*(n+1))+bc v*(n+1)+11

theorem entry (v : Bool) : run0 (table v) 11 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem positive (v : Bool) (n : Nat) : 0 < cost v n := by simp [cost]
theorem growth (v : Bool) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h₁ := out_all v (2*(n+1)) []
  simp only [List.append_nil,pair_rep] at h₁
  rw [show 2*(2*(n+1))=4*n+4 by omega] at h₁
  have h₂ := back_all v n 0
  simp only [Nat.add_zero,List.replicate_zero] at h₂
  have e : bc v*(n+1) = (bc v*(n+1)-1)+1 := by cases v <;> simp [bc] <;> omega
  rw [e,←pad] at h₂
  rw [←e] at h₂
  have h₃ := reset v (ones (4*n+2))
  have h : run0 (table v) (4*n+4+bc v*(n+1)+11) (family n) = some (A (ones (4*n+8)) []) := by
    have h₄ : run0 (table v) (bc v*(n+1)) (A [] (rep (D v) (n+1))) = some (A (false::ones (4*n+4)) (if v then [false] else [])) := by
      simpa only [show 4*(n+1)=4*n+4 by omega] using h₂
    exact join0 (join0 h₁ h₄) h₃
  unfold cost family
  rw [show 2*(2*(n+1))=4*n+4 by omega,show 4*(n+1)+4=4*n+8 by omega]
  exact h

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 11 (cost v) (entry v) (positive v) (growth v) m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108REShared

namespace BB6.Agent10Raw108RE229
open BB6Coverage
def table := BB6.Agent10Raw108REShared.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent10Raw108REShared.never false m hm
end BB6.Agent10Raw108RE229

namespace BB6.Agent10Raw108RE243
open BB6Coverage
def table := BB6.Agent10Raw108REShared.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent10Raw108REShared.never true m hm
end BB6.Agent10Raw108RE243
