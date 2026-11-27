import D1ZeroRD
import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1SixGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

def p : PartialMachine := FAR.fromCodes [7,24,11,24,14,17,6,13,9,22,20,12]

def zz : Nat → List Bool
  | 0 => []
  | n+1 => false::false::zz n

theorem zz_append (i j : Nat) : zz i ++ zz j = zz (i+j) := by
  induction i with
  | zero => simp [zz]
  | succ i ih => simp [zz,ih,Nat.succ_add]

theorem zz_zero (i : Nat) (R : List Bool) : zz i ++ false::R = false::(zz i ++ R) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [zz,ih]

abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b

theorem trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k,join0 hn hk⟩

def DP (k j : Nat) : Prop := ∀ L R,
  Reach (D (zz k ++ true::L) (zz (j+1) ++ true::R))
        (E (zz (k+1) ++ true::L) (zz j ++ true::R))
def EP (k : Nat) : Prop := ∀ L R,
  Reach (E (zz (k+1) ++ true::L) (false::R))
        (E (zz (k+1) ++ true::L) (true::R))

theorem dbase (j : Nat) : DP 0 j := by
  intro L R
  exact ⟨4,rfl⟩

theorem efill (k : Nat) (h : DP k 0) : EP k := by
  intro L R
  apply trans (b := D (zz k ++ true::L) (zz 1 ++ true::R))
  · exact ⟨8,rfl⟩
  · exact h L R

theorem eadvance (k : Nat) (h : EP k) (L R : List Bool) :
    Reach (E (zz (k+1) ++ true::L) (false::false::R))
      (E (zz (k+2) ++ true::L) R) := by
  exact trans (h L (false::R)) ⟨2,rfl⟩

theorem escan (i j : Nat) (h : ∀ k, i ≤ k → k < i+j → EP k) (L R : List Bool) :
    Reach (E (zz (i+1) ++ true::L) (zz j ++ R))
      (E (zz (i+j+1) ++ true::L) R) := by
  induction j generalizing i with
  | zero => exact ⟨0,by rfl⟩
  | succ j ih =>
    have h1 := eadvance i (h i (by omega) (by omega)) L (zz j ++ R)
    have h2 := ih (i+1) (fun k hk hk' => h k (by omega) (by omega))
    have hh := trans h1 h2
    rw [show i+(j+1)+1 = (i+1)+j+1 by omega]
    exact hh

theorem fclear (n : Nat) (L R : List Bool) :
    Reach (F (zz n ++ true::L) R) (D L (false::(zz n ++ R))) := by
  induction n generalizing R with
  | zero => exact ⟨1,rfl⟩
  | succ n ih =>
    have h1 : Reach (F (zz (n+1) ++ true::L) R) (F (zz n ++ true::L) (false::false::R)) := ⟨2,rfl⟩
    have h2 := ih (false::false::R)
    have hh := trans h1 h2
    simpa only [zz,List.cons_append,zz_zero] using hh

theorem dstep (k j : Nat) (he : ∀ i, i ≤ j → EP i) (hk : EP k)
    (hd : DP k (j+1)) : DP (k+1) j := by
  intro L R
  let L' := zz k ++ true::L
  have h1 : Reach (D (zz (k+1) ++ true::L) (zz (j+1) ++ true::R))
      (E (zz 1 ++ true::L') (zz j ++ false::true::R)) := by
    refine ⟨3,?_⟩
    rw [zz_zero]
    rfl
  have h2 : Reach (E (zz 1 ++ true::L') (zz j ++ false::true::R))
      (E (zz (j+1) ++ true::L') (false::true::R)) := by
    simpa only [Nat.zero_add] using escan 0 j (fun i _ hi => he i (by omega)) L' (false::true::R)
  have h3 := he j (by omega) L' (true::R)
  have h4 : Reach (E (zz (j+1) ++ true::L') (true::true::R))
      (F (false::(zz (j+1) ++ true::L')) (true::R)) := ⟨3,rfl⟩
  have h5 : Reach (F (false::(zz (j+1) ++ true::L')) (true::R))
      (F (zz (j+1) ++ true::L') (false::true::R)) := ⟨1,rfl⟩
  have h6 := fclear (j+1) L' (false::true::R)
  have h7 : Reach (D L' (false::(zz (j+1) ++ false::true::R)))
      (E (zz (k+1) ++ true::L) (zz (j+1) ++ true::R)) := by
    simpa only [zz_zero,zz,List.cons_append,L'] using hd L R
  have h8 := eadvance k hk L (zz j ++ true::R)
  exact trans h1 (trans h2 (trans h3 (trans h4 (trans h5 (trans h6 (trans h7 h8))))))

theorem d_all (N : Nat) : ∀ k j, k+j ≤ N → DP k j := by
  induction N with
  | zero =>
    intro k j h
    have : k = 0 := by omega
    subst k
    exact dbase j
  | succ N ih =>
    intro k
    induction k with
    | zero => intro j _; exact dbase j
    | succ k ik =>
      intro j hj
      exact dstep k j (fun i hi => efill i (ih i 0 (by omega)))
        (efill k (ih k 0 (by omega))) (ik (j+1) (by omega))

theorem e_all (k : Nat) : EP k := efill k (d_all k k 0 (by omega))

def family (k : Nat) : Z0 := E (zz (k+1) ++ [true,false,true]) []
theorem first : run0 p 8 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem growth (k : Nat) : ∃ t, 0 < t ∧ run0 p t (family k) = some (family (k+1)) := by
  have h1 : run0 p 8 (family k) = some (D (zz k ++ [true,false,true]) [false,false,true]) := by rfl
  obtain ⟨t,ht⟩ := d_all k k 0 (by omega) [false,true] []
  have h2 : run0 p 2 (E (zz (k+1) ++ [true,false,true]) [true]) = some (family (k+1)) := rfl
  exact ⟨8+t+2,by omega,join0 (join0 h1 ht) h2⟩

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  classical
  let cost (k : Nat) := Classical.choose (growth k)
  exact never_of_growth p family 8 cost first
    (fun k => (Classical.choose_spec (growth k)).1)
    (fun k => (Classical.choose_spec (growth k)).2) m hm

theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms never
#print axioms cover
end BB6.Agent6D1SixGrowth
