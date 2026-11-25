import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110UnaryCounter
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LA_1RC1RF_0RD1LF_1LD1RE_---0LC_1LA0RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
abbrev P (n : Nat) := rep [true,true] n
abbrev Z (n : Nat) := rep [false,false] n
def X (n : Nat) (L R : List Bool) : Z0 := ⟨5,false :: (P (n+2) ++ false::L),R⟩
def Y (j : Nat) (L R : List Bool) : Z0 := ⟨5,false :: false :: (P (j+1) ++ false::L),R⟩
def out (n : Nat) (L R : List Bool) : Z0 := ⟨5,R.headD false :: false :: (P (n+2) ++ false::L),R.tail⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem two (L R : List Bool) : run0 table 2 ⟨0,[true,true]++L,R⟩ = some ⟨0,L,[false,false]++R⟩ := by rfl
theorem process (k j : Nat) (L R : List Bool)
    (prev : ∀ i, i < j+k → ∀ L R, Reaches (X i L R) (out i L R)) :
    Reaches (Y j L (Z k ++ R)) (Y (j+k) L R) := by
  induction k generalizing j with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 : Reaches (Y j L (Z (k+1)++R)) (X j L (false::(Z k++R))) := ⟨3,by rfl⟩
    have h2 := prev j (by omega) L (false::(Z k++R))
    have h3 := ih (j+1) (fun i hi => prev i (by omega))
    rw [show j+1+k = j+(k+1) by omega] at h3
    exact trans h1 (trans h2 h3)
theorem counter (n : Nat) (L R : List Bool) : Reaches (X n L R) (out n L R) := by
  induction n using Nat.strongRecOn generalizing L R with
  | ind n ih =>
    have h1 : run0 table 1 (X n L R) = some ⟨0,P (n+2)++false::L,true::R⟩ := by rfl
    have h2 := sweepL table 0 [] [] [true,true] [false,false] 2 two (n+2) (false::L) (true::R)
    simp only [List.nil_append] at h2
    have h3 : run0 table 14 ⟨0,false::L,Z (n+2)++true::R⟩ = some (Y 0 L (Z n++true::R)) := by rfl
    have h4 := process n 0 L (true::R) (fun i hi L R => ih i (by omega) L R)
    simp only [Nat.zero_add] at h4
    have h5 : run0 table 4 (Y n L (true::R)) = some (out n L R) := by rfl
    exact trans ⟨_,join0 (join0 h1 h2) h3⟩ (trans h4 ⟨4,h5⟩)
def family (n : Nat) : Z0 := X n [] []
theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,h⟩ := counter n [] []
  have h' : run0 table 3 (out n [] []) = some (family (n+1)) := by rfl
  exact ⟨t+3,by omega,join0 h h'⟩
noncomputable def cost (n : Nat) : Nat := (growth_exists n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (growth_exists n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (growth_exists n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent7Raw110UnaryCounter
