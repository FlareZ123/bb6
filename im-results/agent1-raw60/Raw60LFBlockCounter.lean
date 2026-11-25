import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFBlockCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev C := Q 2
abbrev D := Q 3
abbrev Z (n : Nat) := List.replicate n false
abbrev B : List Bool := [true,true,true,true,false]
abbrev K : List Bool := [false,false,false,true,true]
abbrev J : List Bool := [false,true,true,false,false]
abbrev V : List Bool := [true,true,false,true,false]
abbrev M : List Bool := [true,false,false,true,true,true,false]
abbrev E : List Bool := [true,true,true,true,true]
abbrev P : List Bool := [false,false,true,true,true,true]
abbrev pad : List Bool := [false,false]

def rep (w : List Bool) : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => w++rep w n R

theorem repEnd (w : List Bool) (n : Nat) (R : List Bool) : rep w n (w++R)=rep w (n+1) R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih]

def W (n k : Nat) := U (2*n+3)++false::rep B (k+1) E

theorem zmerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem cSweep (n : Nat) (L R : List Bool) :
    run0 table n (C (true::L) (U n++R)) = some (C (true::(Z n++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (C (true::L) (U (n+1)++R)) = some (C (true::false::L) (U n++R)) := by rfl
    have H := join0 h (ih (false::L))
    have he : Z n++false::L=Z (n+1)++L := by
      change Z n++(Z 1++L)=_
      rw [zmerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H

theorem pack (k : Nat) (L : List Bool) : Reach table (F (Z 4++L) (V++rep B k E)) (D (P++rep K (k+2) (pad++L)) []) := by
  induction k generalizing L with
  | zero => exact ⟨26,by rfl⟩
  | succ k ih =>
    have h1 : run0 table 15 (F (Z 4++L) (V++rep B (k+1) E)) = some (F (Z 4++(J++L)) (V++rep B k E)) := by rfl
    have h2 := ih (J++L)
    have he : pad++(J++L)=K++(pad++L) := by rfl
    rw [he,repEnd K (k+2) (pad++L)] at h2
    exact reachTrans ⟨15,h1⟩ h2

theorem unpackLoop (k : Nat) (L R : List Bool) : Reach table (F (rep K k L) (M++R)) (F L (M++rep B k R)) := by
  induction k generalizing R with
  | zero => exact ⟨0,by rfl⟩
  | succ k ih =>
    have h1 : run0 table 17 (F (rep K (k+1) L) (M++R)) = some (F (rep K k L) (M++(B++R))) := by rfl
    have h2 := ih (B++R)
    rw [repEnd B k R] at h2
    exact reachTrans ⟨17,h1⟩ h2

theorem unpack (k : Nat) (L : List Bool) : Reach table (D (P++rep K (k+2) (pad++L)) []) (F L (W 0 (k+1))) := by
  have h1 : run0 table 10 (D (P++rep K (k+2) (pad++L)) []) = some (F (rep K (k+2) (pad++L)) (E++[false])) := by rfl
  have h2 : run0 table 25 (F (rep K (k+2) (pad++L)) (E++[false])) = some (F (rep K (k+1) (pad++L)) (M++E)) := by rfl
  have h3 := unpackLoop (k+1) (pad++L) E
  have h4 : run0 table 14 (F (pad++L) (M++rep B (k+1) E)) = some (F L (W 0 (k+1))) := by rfl
  exact reachTrans ⟨10,h1⟩ (reachTrans ⟨25,h2⟩ (reachTrans h3 ⟨14,h4⟩))

theorem clear (n k : Nat) (L : List Bool) : ∃ t, 2≤t ∧ run0 table t (F (pad++L) (W n k)) = some (F (Z (2*n)++true::true::L) (W 0 (k+1))) := by
  have h1 : run0 table 3 (F (pad++L) (W n k)) = some (C (true::true::true::L) (U (2*n+2)++false::rep B (k+1) E)) := by rfl
  have h2 := cSweep (2*n+2) (true::true::L) (false::rep B (k+1) E)
  have h3 : run0 table 7 (C (true::(Z (2*n+2)++true::true::L)) (false::rep B (k+1) E)) = some (F (Z (2*n+4)++true::true::L) (V++rep B k E)) := by rfl
  obtain ⟨a,ha⟩ := pack k (Z (2*n)++true::true::L)
  obtain ⟨b,hb⟩ := unpack k (Z (2*n)++true::true::L)
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) ha) hb⟩

def Inc (n : Nat) : Prop := ∀ k L, ∃ k' t, 2≤t ∧ run0 table t (F (pad++L) (W n k)) = some (F L (W (n+1) k'))

theorem chain (d j k : Nat) (L : List Bool) (h : ∀ i, j≤i → i<j+d → Inc i) :
    ∃ k', Reach table (F (Z (2*d)++L) (W j k)) (F L (W (j+d) k')) := by
  induction d generalizing j k with
  | zero => exact ⟨k,0,by rfl⟩
  | succ d ih =>
    obtain ⟨k',t,_,ht⟩ := h j (by omega) (by omega) k (Z (2*d)++L)
    obtain ⟨k'',h2⟩ := ih (j+1) k' (fun i hi hi' => h i (by omega) (by omega))
    rw [show j+1+d=j+(d+1) by omega] at h2
    exact ⟨k'',reachTrans ⟨t,ht⟩ h2⟩

theorem inc (n : Nat) : Inc n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k L
    obtain ⟨a,apos,h1⟩ := clear n k L
    obtain ⟨k',b,h2⟩ := chain n 0 (k+1) (true::true::L) (fun i _ hi => ih i (by omega))
    rw [Nat.zero_add] at h2
    have h3 : run0 table 2 (F (true::true::L) (W n k')) = some (F L (W (n+1) k')) := by rfl
    exact ⟨k',_,by omega,join0 (join0 h1 h2) h3⟩

theorem firstEq (R : List Bool) : run0 table 2 (F [] R)=run0 table 2 (F pad R) := by cases R <;> rfl

theorem transfer (R : List Bool) (t : Nat) (h : 2≤t) (c : Z0)
    (hr : run0 table t (F pad R)=some c) : run0 table t (F [] R)=some c := by
  have ht : t=2+(t-2) := by omega
  rw [ht,run0_add,firstEq,←run0_add,←ht]
  exact hr

theorem advance (n k : Nat) : ∃ k' t, 0<t ∧ run0 table t (F [] (W n k)) = some (F [] (W (n+1) k')) := by
  obtain ⟨k',t,hpos,h⟩ := inc n k []
  exact ⟨k',t,by omega,transfer _ _ hpos _ h⟩
noncomputable def nextK (n k : Nat) := Classical.choose (advance n k)
noncomputable def size : Nat → Nat
  | 0 => 0
  | n+1 => nextK (n+3) (size n)
noncomputable def family (n : Nat) := F [] (W (n+3) (size n))
theorem entry : run0 table 179 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h := Classical.choose_spec (advance (n+3) (size n))
  have he : n+3+1=n+1+3 := by omega
  change ∃ t, 0<t ∧ run0 table t (F [] (W (n+3) (size n))) = some (F [] (W (n+1+3) (size (n+1))))
  rw [←he]
  exact h
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 179 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFBlockCounter
