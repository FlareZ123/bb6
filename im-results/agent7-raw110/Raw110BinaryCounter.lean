import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110BinaryCounter
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1LF_1RC0RB_0RD0LA_1LD1RE_0LE0LC_1LA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none
abbrev P (n : Nat) := rep [true,true] n
abbrev Z (n : Nat) := rep [false,false] n
abbrev marker : List Bool := [false,false,true,false]
def X (n : Nat) (L : List Bool) : Z0 := ⟨0,false::L,P n++marker⟩
def Y (n : Nat) (L : List Bool) : Z0 := ⟨0,true::L,P n++marker⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem two (L R : List Bool) : run0 table 2 ⟨1,[true]++L,[true,true]++R⟩ = some ⟨1,[true]++[false,false]++L,R⟩ := by rfl
theorem pre (n : Nat) (L : List Bool) : Reaches (X (n+1) L) ⟨0,Z (n+1)++true::L,marker⟩ := by
  have h1 : run0 table 1 (X (n+1) L) = some ⟨1,[true,true]++L,true::(P n++marker)⟩ := by rfl
  have h2 := sweepR table 1 [true] [] [true,true] [false,false] 2 two n (true::L) (true::marker)
  have h2' : run0 table (2*n) ⟨1,[true,true]++L,true::(P n++marker)⟩ = some ⟨1,true::(Z n++true::L),true::marker⟩ := by
    have hrot : ∀ k, true::(P k++marker) = P k++true::marker := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [rep,List.cons_append,List.nil_append]; rw [ih]
    rw [hrot]; exact h2
  have h3 : run0 table 13 ⟨1,true::(Z n++true::L),true::marker⟩ = some ⟨0,Z (n+1)++true::L,marker⟩ := by rfl
  exact ⟨_,join0 (join0 h1 h2') h3⟩
theorem process (k j : Nat) (L : List Bool)
    (prev : ∀ i, i < j+k → ∀ L, Reaches (X i L) (Y i L)) :
    Reaches ⟨0,Z k++true::L,P j++marker⟩ (Y (j+k) L) := by
  induction k generalizing j with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 := prev j (by omega) (false::(Z k++true::L))
    have h2 : run0 table 2 (Y j (false::(Z k++true::L))) = some ⟨0,Z k++true::L,P (j+1)++marker⟩ := by rfl
    have h3 := ih (j+1) (fun i hi => prev i (by omega))
    rw [show j+1+k=j+(k+1) by omega] at h3
    exact trans h1 (trans ⟨2,h2⟩ h3)
theorem counter (n : Nat) (L : List Bool) : Reaches (X n L) (Y n L) := by
  induction n using Nat.strongRecOn generalizing L with
  | ind n ih =>
    cases n with
    | zero => exact ⟨12,rfl⟩
    | succ n =>
      have h1 := pre n L
      have h2 := process (n+1) 0 L (fun i hi L => ih i (by omega) L)
      simp only [Nat.zero_add] at h2
      exact trans h1 h2
def family (n : Nat) : Z0 := ⟨0,[],P (n+2)++marker⟩
theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem grow (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,h⟩ := counter (n+2) []
  cases t with
  | zero => simp [run0,X,Y] at h
  | succ t =>
    have h1 : run0 table (t+1) (family n) = some (Y (n+2) []) := h
    have h2 : run0 table 2 (Y (n+2) []) = some (family (n+1)) := by rfl
    exact ⟨t+1+2,by omega,join0 h1 h2⟩
noncomputable def cost (n : Nat) : Nat := (grow n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (grow n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (grow n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family 40 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent7Raw110BinaryCounter
