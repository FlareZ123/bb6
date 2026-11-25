import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFPairCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => if v then some (some ⟨false,true,5⟩) else some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev C := Q 2
abbrev Z (n : Nat) := List.replicate n false
def W (n : Nat) (R : List Bool) := U (2*n+3)++false::true::true::true::true::false::true::true::true::true::true::R

theorem zmerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]
theorem cSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n (C (true::L) (U n++R)) = some (C (true::(Z n++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (C (true::L) (U (n+1)++R)) = some (C (true::false::L) (U n++R)) := by cases v <;> rfl
    have H := join0 h (ih (false::L))
    have he : Z n++false::L=Z (n+1)++L := by
      change Z n++(Z 1++L)=_
      rw [zmerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H

def extra (v : Bool) := if v then 40 else 38

theorem clear (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (3+(2*n+2)+7+extra v) (F (false::false::L) (W n R)) = some (F (Z (2*n)++true::true::L) (W 0 R)) := by
  have h1 : run0 (table v) 3 (F (false::false::L) (W n R)) = some (C (true::true::true::L) (U (2*n+2)++false::true::true::true::true::false::true::true::true::true::true::R)) := by cases v <;> rfl
  have h2 := cSweep v (2*n+2) (true::true::L) (false::true::true::true::true::false::true::true::true::true::true::R)
  have h3 : run0 (table v) 7 (C (true::(Z (2*n+2)++true::true::L)) (false::true::true::true::true::false::true::true::true::true::true::R)) = some (F (Z (2*n+4)++true::true::L) (true::true::false::true::false::true::true::true::true::true::R)) := by cases v <;> rfl
  have h4 : run0 (table v) (extra v) (F (Z (2*n+4)++true::true::L) (true::true::false::true::false::true::true::true::true::true::R)) = some (F (Z (2*n)++true::true::L) (W 0 R)) := by cases v <;> rfl
  exact join0 (join0 (join0 h1 h2) h3) h4

def Inc (v : Bool) (n : Nat) : Prop := ∀ L R : List Bool,
  ∃ t, 2≤t ∧ run0 (table v) t (F (false::false::L) (W n R)) = some (F L (W (n+1) R))

theorem chain (v : Bool) (d j : Nat) (L R : List Bool) (h : ∀ i, j≤i → i<j+d → Inc v i) :
    Reach (table v) (F (Z (2*d)++L) (W j R)) (F L (W (j+d) R)) := by
  induction d generalizing j with
  | zero => exact ⟨0,by rfl⟩
  | succ d ih =>
    obtain ⟨t,_,ht⟩ := h j (by omega) (by omega) (Z (2*d)++L) R
    have h2 := ih (j+1) (fun i hi hi' => h i (by omega) (by omega))
    rw [show j+1+d=j+(d+1) by omega] at h2
    exact reachTrans ⟨t,ht⟩ h2

theorem inc (v : Bool) (n : Nat) : Inc v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L R
    have h1 := clear v n L R
    obtain ⟨t,h2⟩ := chain v n 0 (true::true::L) R (fun i _ hi => ih i (by omega))
    rw [Nat.zero_add] at h2
    have h3 : run0 (table v) 2 (F (true::true::L) (W n R)) = some (F L (W (n+1) R)) := by cases v <;> rfl
    exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem firstEq (v : Bool) (R : List Bool) : run0 (table v) 2 (F [] R)=run0 (table v) 2 (F [false,false] R) := by cases v <;> cases R <;> rfl

theorem transfer (v : Bool) (R : List Bool) (t : Nat) (h : 2≤t) (c : Z0)
    (hr : run0 (table v) t (F [false,false] R)=some c) : run0 (table v) t (F [] R)=some c := by
  have ht : t=2+(t-2) := by omega
  rw [ht,run0_add,firstEq,←run0_add,←ht]
  exact hr

def family (n : Nat) := F [] (W (n+3) [])
theorem entry (v : Bool) : run0 (table v) 179 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth_exists (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family n) = some (family (n+1)) := by
  obtain ⟨t,hpos,h⟩ := inc v (n+3) [] []
  have he : n+3+1=n+1+3 := by omega
  rw [he] at h
  exact ⟨t,by omega,transfer v _ t hpos _ h⟩
noncomputable def cost (v : Bool) (n : Nat) : Nat := Classical.choose (growth_exists v n)
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 179 (cost v) (entry v) (fun n => (Classical.choose_spec (growth_exists v n)).1)
    (fun n => (Classical.choose_spec (growth_exists v n)).2) m hm
namespace Leaf984
abbrev table := BB6.Agent1Raw60LFPairCounter.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPairCounter.never false m hm
#print axioms never
end Leaf984
namespace Leaf988
abbrev table := BB6.Agent1Raw60LFPairCounter.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFPairCounter.never true m hm
#print axioms never
end Leaf988
end BB6.Agent1Raw60LFPairCounter
