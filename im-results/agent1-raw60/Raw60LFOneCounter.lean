import SweepPumping
namespace BB6.Agent1Raw60LFOneCounter
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

abbrev U (n : Nat) := List.replicate n true
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev Reach (a b : Z0) := ∃ t : Nat, run0 table t a = some b

theorem trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨t+u,join0 ht hu⟩

theorem merge (a b : Nat) (L : List Bool) : U a++(U b++L) = U (a+b)++L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem sweepC (k : Nat) (L R : List Bool) :
    run0 table k (C (U k++L) R) = some (C L (U k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 (C (U (k+1)++L) R) = some (C (U k++L) (true::R)) := by rfl
    have H := join0 h (ih (true::R))
    have he : U k++true::R=U (k+1)++R := by rw [← merge k 1]; rfl
    rw [he,Nat.add_comm 1 k] at H
    exact H

theorem clear (k : Nat) (L R : List Bool) :
    Reach (D (U (k+1)++false::L) (true::true::R))
      (D (true::false::L) (U k++false::false::R)) := by
  have h1 : run0 table 4 (D (U (k+1)++false::L) (true::true::R)) =
      some (C (U (k+1)++false::L) (false::false::R)) := by rfl
  have h2 := sweepC (k+1) (false::L) (false::false::R)
  have h3 : run0 table 1 (C (false::L) (U (k+1)++false::false::R)) =
      some (D (true::false::L) (U k++false::false::R)) := by rfl
  exact ⟨_,join0 (join0 h1 h2) h3⟩

def K (n : Nat) := 3*n+1

def Fill (n : Nat) : Prop := ∀ L R : List Bool,
    Reach (D (U (K n)++false::L) (true::true::R))
      (F (false::(U (K n+1)++false::L)) R)

theorem chain (d j : Nat) (L R : List Bool)
    (hfill : ∀ i, j≤i → i<j+d → Fill i) :
    Reach (D (U (K j)++false::L) (U (3*d)++R))
      (D (U (K (j+d))++false::L) R) := by
  induction d generalizing j with
  | zero => exact ⟨0,by rfl⟩
  | succ d ih =>
    have h1 := hfill j (by omega) (by omega) L (true::(U (3*d)++R))
    have h2 : run0 table 1 (F (false::(U (K j+1)++false::L)) (true::(U (3*d)++R))) =
        some (D (U (K (j+1))++false::L) (U (3*d)++R)) := by
      rw [show K (j+1)=K j+1+1+1 by unfold K; omega]
      rfl
    have h3 := ih (j+1) (fun i hi hi' => hfill i (by omega) (by omega))
    rw [show j+1+d=j+(d+1) by omega] at h3
    exact trans h1 (trans ⟨1,h2⟩ h3)

theorem fill (n : Nat) : Fill n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L R
    have h1 := clear (3*n) L R
    have h2 := chain n 0 L (false::false::R) (fun i _ hi => ih i (by omega))
    rw [Nat.zero_add] at h2
    have h3 : run0 table 2 (D (U (K n)++false::L) (false::false::R)) =
        some (F (false::(U (K n+1)++false::L)) R) := by unfold K; rfl
    exact trans h1 (trans h2 ⟨2,h3⟩)

def family (n : Nat) : Z0 := D (false::false::(U (3*n+9)++[false])) []

theorem entry : run0 table 46 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h0 : run0 table 2 (family n) = some (D (U (3*n+9)++[false]) [true,true]) := by rfl
  obtain ⟨a,h1⟩ := clear (3*n+8) [] []
  have he : U (3*n+8)++[false,false] = U (3*(n+2))++[true,true,false,false] := by
    rw [show 3*n+8=3*(n+2)+2 by omega,← merge (3*(n+2)) 2]; rfl
  rw [he] at h1
  obtain ⟨b,h2⟩ := chain (n+2) 0 [] [true,true,false,false] (fun i _ _ => fill i)
  rw [Nat.zero_add] at h2
  obtain ⟨c,h3⟩ := fill (n+2) [] [false,false]
  have h4 : run0 table 7 (F (false::(U (K (n+2)+1)++[false])) [false,false]) =
      some (family (n+1)) := by
    unfold family K
    rw [show 3*(n+1)+9=3*(n+2)+1+1+1+1+1+1 by omega]
    rfl
  exact ⟨2+a+b+c+7,by omega,join0 (join0 (join0 (join0 h0 h1) h2) h3) h4⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 46 cost entry
    (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms fill
#print axioms growth_exists
#print axioms never
end BB6.Agent1Raw60LFOneCounter
