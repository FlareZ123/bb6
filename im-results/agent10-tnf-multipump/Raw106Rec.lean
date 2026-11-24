import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Recursive.R106M1113
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC1RF_0RD1LC_1LD1RE_---0LB_1RA1RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
def A (m : Nat) (R : List Bool) : Z0 := ⟨0,O m ++ [false],R⟩
def Z (m : Nat) (R : List Bool) : Z0 := ⟨0,false::(O m ++ [false]),R⟩
def D (m : Nat) : Z0 := ⟨3,false::false::(O m ++ [false]),[]⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem rep_one (n : Nat) : rep [true] n = O n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]
theorem Cstep (L R : List Bool) : run0 table 1 ⟨2,[true]++L,R⟩ = some ⟨2,L,[true]++R⟩ := by rfl
theorem splitA (n : Nat) (R : List Bool) : Reaches (A (n+4) R) (A 3 (O n ++ false::R)) := by
  have h1 : run0 table 1 (A (n+4) R) = some ⟨2,O (n+3)++[false],false::R⟩ := by rfl
  have h2 := sweepL table 2 [] [] [true] [true] 1 Cstep (n+3) [false] (false::R)
  simp only [List.nil_append,rep_one,Nat.one_mul] at h2
  have h3 : run0 table 5 ⟨2,[false],O (n+3)++false::R⟩ = some (A 3 (O n++false::R)) := by rfl
  exact ⟨1+(n+3)+5,join0 (join0 h1 h2) h3⟩
theorem baseA (R : List Bool) : Reaches (A 3 R) (Z 2 R) := ⟨8,rfl⟩
theorem advance (m : Nat) (R : List Bool) : Reaches (Z m ([true,true,true,true,true]++R)) (A (m+6) R) := ⟨7,rfl⟩
theorem finish (m : Nat) (R : List Bool) : Reaches (Z m ([true,true,true,true,false]++R)) (Z (m+5) R) := ⟨7,rfl⟩
-- Given previously proved A-return lemmas up to j+t, process t full blocks and one final block.
theorem blocks (t j : Nat) (R : List Bool)
    (prev : ∀ k, 0 < k → k ≤ j+t → ∀ X, Reaches (A (5*k+3) X) (Z (5*k+2) X)) :
    Reaches (Z (5*j+2) (O (5*t+4)++false::R)) (Z (5*(j+t+1)+2) R) := by
  induction t generalizing j with
  | zero =>
    have h := finish (5*j+2) R
    rw [show 5*(j+0+1)+2 = 5*j+2+5 by omega]
    exact h
  | succ t ih =>
    have h1 := advance (5*j+2) (O (5*t+4)++false::R)
    have h1' : Reaches (Z (5*j+2) (O (5*(t+1)+4)++false::R)) (A (5*(j+1)+3) (O (5*t+4)++false::R)) := by
      rw [show 5*(t+1)+4 = (5*t+4)+5 by omega,show 5*(j+1)+3 = 5*j+2+6 by omega]
      exact h1
    have h2 := prev (j+1) (by omega) (by omega) (O (5*t+4)++false::R)
    have h3 := ih (j+1) (fun k hk hle => prev k hk (by omega))
    rw [show j+1+t+1=j+(t+1)+1 by omega] at h3
    exact trans h1' (trans h2 h3)
theorem allA (k : Nat) : ∀ R, Reaches (A (5*k+3) R) (Z (5*k+2) R) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro R
    cases k with
    | zero => exact baseA R
    | succ k =>
      have h1 := splitA (5*k+4) R
      rw [show 5*k+4+4=5*(k+1)+3 by omega] at h1
      have h2 := baseA (O (5*k+4)++false::R)
      have h3 := blocks k 0 R (fun i _ hi => ih i (by omega))
      simp only [Nat.mul_zero,Nat.zero_add] at h3
      exact trans h1 (trans h2 h3)
theorem fullBlocks (t j r : Nat) (R : List Bool) :
    Reaches (Z (5*j+2) (O (5*t+r)++false::R)) (Z (5*(j+t)+2) (O r++false::R)) := by
  induction t generalizing j with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ t ih =>
    have h1 := advance (5*j+2) (O (5*t+r)++false::R)
    have h1' : Reaches (Z (5*j+2) (O (5*(t+1)+r)++false::R)) (A (5*(j+1)+3) (O (5*t+r)++false::R)) := by
      rw [show 5*(t+1)+r=5*t+r+5 by omega,show 5*(j+1)+3=5*j+2+6 by omega]
      exact h1
    have h2 := allA (j+1) (O (5*t+r)++false::R)
    have h3 := ih (j+1)
    rw [show j+1+t=j+(t+1) by omega] at h3
    exact trans h1' (trans h2 h3)
theorem Arem (k r : Nat) : Reaches (A (5*k+4+r) []) (Z (5*k+2) (O r++[false])) := by
  have h1 := splitA (5*k+r) []
  have h2 := baseA (O (5*k+r)++[false])
  have h3 := fullBlocks k 0 r []
  simp only [Nat.mul_zero,Nat.zero_add] at h3
  rw [show 5*k+r+4=5*k+4+r by omega] at h1
  exact trans h1 (trans h2 h3)
theorem startD (m : Nat) : run0 table 6 (D (m+2)) = some (A (m+4) []) := by rfl
theorem finish0 (k : Nat) : Reaches (Z (5*k+2) [false]) (D (5*k+4)) := ⟨3,rfl⟩
theorem finish1 (k : Nat) : Reaches (Z (5*k+2) [true,false]) (D (5*k+7)) := ⟨6,rfl⟩
theorem finish2 (k : Nat) : Reaches (Z (5*k+2) [true,true,false]) (D (5*k+8)) := ⟨11,rfl⟩
theorem D0 (k : Nat) : ∃ t, 0<t ∧ run0 table t (D (5*k+2)) = some (D (5*k+4)) := by
  have h1 := startD (5*k)
  obtain ⟨t,h2⟩ := trans (Arem k 0) (finish0 k)
  exact ⟨6+t,by omega,join0 h1 h2⟩
theorem D1 (k : Nat) : ∃ t, 0<t ∧ run0 table t (D (5*k+3)) = some (D (5*k+7)) := by
  have h1 := startD (5*k+1)
  obtain ⟨t,h2⟩ := trans (Arem k 1) (finish1 k)
  rw [show 5*k+1+2=5*k+3 by omega,show 5*k+1+4=5*k+4+1 by omega] at h1
  exact ⟨6+t,by omega,join0 h1 h2⟩
theorem D2 (k : Nat) : ∃ t, 0<t ∧ run0 table t (D (5*k+4)) = some (D (5*k+8)) := by
  have h1 := startD (5*k+2)
  obtain ⟨t,h2⟩ := trans (Arem k 2) (finish2 k)
  rw [show 5*k+2+2=5*k+4 by omega,show 5*k+2+4=5*k+4+2 by omega] at h1
  exact ⟨6+t,by omega,join0 h1 h2⟩
-- A complete three-return epoch increments the D section by ten.
theorem epoch (n : Nat) : ∃ t, 0<t ∧ run0 table t (D (10*n+4)) = some (D (10*(n+1)+4)) := by
  obtain ⟨a,ha,h1⟩ := D2 (2*n)
  obtain ⟨b,hb,h2⟩ := D1 (2*n+1)
  obtain ⟨c,hc,h3⟩ := D0 (2*n+2)
  rw [show 5*(2*n)+4=10*n+4 by omega,show 5*(2*n)+8=5*(2*n+1)+3 by omega] at h1
  rw [show 5*(2*n+1)+7=5*(2*n+2)+2 by omega] at h2
  rw [show 5*(2*n+2)+4=10*(n+1)+4 by omega] at h3
  exact ⟨a+b+c,by omega,join0 (join0 h1 h2) h3⟩
def family (n : Nat) := D (10*n+4)
theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem family_step (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := epoch n
noncomputable def cost (n : Nat) : Nat := (family_step n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (family_step n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (family_step n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 29 cost entry cost_pos growth m hm
#print axioms allA
#print axioms epoch
#print axioms never
end BB6.Agent10Recursive.R106M1113
