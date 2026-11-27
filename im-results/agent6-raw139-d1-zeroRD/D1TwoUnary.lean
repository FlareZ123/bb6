import Raw139Normalized
import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1TwoUnary
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

def p (w : Bool) : PartialMachine := FAR.fromCodes
  (if w then [7,8,11,19,14,0,2,13,23,24,15,2]
        else [7,0,11,19,14,8,2,13,23,24,15,10])

abbrev oo := rep [true,true]
abbrev zz := rep [false,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def B (k : Nat) (L R : List Bool) : Z0 := ⟨1,oo (2*k+1) ++ false::L,R⟩
def Reach (w : Bool) (a b : Z0) : Prop := ∃ t, run0 (p w) t a = some b

theorem trans {w : Bool} {a b c : Z0} (h : Reach w a b) (g : Reach w b c) : Reach w a c := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k,join0 hn hk⟩

theorem zz_zero (n : Nat) (R : List Bool) : zz n ++ false::R = false::(zz n ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih]

theorem zz_add (i j : Nat) : zz (i+j) = zz i ++ zz j := by
  induction i with
  | zero => simp [rep]
  | succ i ih => simp [rep,Nat.succ_add,ih]

variable (w : Bool)

theorem sweepA (n : Nat) (L R : List Bool) :
    Reach w (A (oo n ++ L) R) (A L (zz n ++ R)) := by
  refine ⟨2*n,?_⟩
  have H := sweepL (p w) 0 [] [] [true,true] [false,false] 2
    (by intro X Y; cases w <;> rfl) n L R
  simpa only [List.nil_append] using H

theorem sweepC (n : Nat) (L R : List Bool) :
    Reach w (C (oo n ++ L) R) (C L (zz n ++ R)) := by
  refine ⟨2*n,?_⟩
  have H := sweepL (p w) 2 [] [] [true,true] [false,false] 2
    (by intro X Y; cases w <;> rfl) n L R
  simpa only [List.nil_append] using H

def G (w : Bool) (k : Nat) : Prop := ∀ L R,
  Reach w (B k L (zz 2 ++ R)) (B (k+1) L R)

theorem repeatG (i j : Nat) (h : ∀ k, i ≤ k → k < i+j → G w k) (L R : List Bool) :
    Reach w (B i L (zz (2*j) ++ R)) (B (i+j) L R) := by
  induction j generalizing i with
  | zero => exact ⟨0,rfl⟩
  | succ j ih =>
    have h1 := h i (by omega) (by omega) L (zz (2*j) ++ R)
    have h2 := ih (i+1) (fun k hk hk' => h k (by omega) (by omega))
    have hh := trans h1 h2
    rw [show i+(j+1)=(i+1)+j by omega]
    simpa only [show 2*(j+1)=2+2*j by omega,zz_add,List.append_assoc] using hh

/-- The middle recursion is independent of whether the final right-hand
    zero is explicit or belongs to the implicit blank half-line. -/
theorem middle (k : Nat) (h : ∀ i, i < k → G w i) (L S : List Bool) :
    Reach w (A (oo (2*k+2) ++ false::L) (true::S))
      (B k L (false::false::true::S)) := by
  have h1 := sweepA w (2*k+2) (false::L) (true::S)
  have h2 : Reach w (A (false::L) (zz (2*k+2) ++ true::S))
      (B 0 (true::L) (zz (2*k) ++ false::true::S)) := by
    refine ⟨7,?_⟩
    rw [zz_zero]
    cases w <;> rfl
  have h3 := repeatG w 0 k (fun i _ hi => h i (by omega)) (true::L) (false::true::S)
  have h3' : Reach w (B 0 (true::L) (zz (2*k) ++ false::true::S))
      (B k (true::L) (false::true::S)) := by simpa only [Nat.zero_add] using h3
  have h4 : Reach w (B k (true::L) (false::true::S))
      (C (oo (2*k+1) ++ false::true::L) (false::true::S)) := ⟨4,by cases w <;> rfl⟩
  have h5 := sweepC w (2*k+1) (false::true::L) (false::true::S)
  have h6 : Reach w (C (false::true::L) (zz (2*k+1) ++ false::true::S))
      (B 0 L (zz (2*k+1) ++ true::S)) := by
    refine ⟨5,?_⟩
    rw [zz_zero]
    cases w <;> rfl
  have h7 := repeatG w 0 k (fun i _ hi => h i (by omega)) L (false::false::true::S)
  have h7' : Reach w (B 0 L (zz (2*k+1) ++ true::S))
      (B k L (false::false::true::S)) := by
    rw [zz_add (2*k) 1]
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_add] using h7
  exact trans h1 (trans h2 (trans h3' (trans h4 (trans h5 (trans h6 h7')))))

theorem gstep (k : Nat) (h : ∀ i, i < k → G w i) : G w k := by
  intro L R
  have h1 : Reach w (B k L (zz 2 ++ R))
      (A (oo (2*k+2) ++ false::L) (true::false::R)) := ⟨4,by cases w <;> rfl⟩
  have h2 := middle w k h L (false::R)
  have h3 : Reach w (B k L (false::false::true::false::R)) (B (k+1) L R) := by
    refine ⟨6,?_⟩
    unfold B
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega]
    cases w <;> rfl
  exact trans h1 (trans h2 h3)

theorem allGle (n : Nat) : ∀ k, k ≤ n → G w k := by
  induction n with
  | zero => intro k hk; exact gstep w k (by intro i hi; omega)
  | succ n ih =>
    intro k hk
    by_cases h : k ≤ n
    · exact ih k h
    · exact gstep w k (fun i hi => ih i (by omega))

theorem allG (k : Nat) : G w k := allGle w k k (by omega)

def family (k : Nat) : Z0 := B k [true] []

theorem entry : run0 (p w) 7 ⟨0,[],[]⟩ = some (family 0) := by cases w <;> rfl

theorem growth (k : Nat) : ∃ t, 0 < t ∧ run0 (p w) t (family k) = some (family (k+1)) := by
  have h1 : run0 (p w) 4 (family k) = some (A (oo (2*k+2) ++ [false,true]) [true]) := by cases w <;> rfl
  obtain ⟨t,ht⟩ := middle w k (fun i _ => allG w i) [true] []
  have h3 : run0 (p w) 6 (B k [true] [false,false,true]) = some (family (k+1)) := by
    unfold family
    unfold B
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega]
    cases w <;> rfl
  exact ⟨4+t+6,by omega,join0 (join0 h1 ht) h3⟩

theorem never (m : Machine) (hm : compatible (p w) m) : NeverHalts m := by
  classical
  let cost (k : Nat) := Classical.choose (growth w k)
  exact never_of_growth (p w) family 7 cost (entry w)
    (fun k => (Classical.choose_spec (growth w k)).1)
    (fun k => (Classical.choose_spec (growth w k)).2) m hm

theorem cover (B : Nat) : Cover (WeightedBound B) (p w) :=
  .leaf (p w) (fun m hm => weighted_never B m (never w m hm))

theorem cover354 (B : Nat) : Cover (WeightedBound B) (FAR.fromCodes [7,0,11,19,14,8,2,13,23,24,15,10]) := cover false B
theorem cover355 (B : Nat) : Cover (WeightedBound B) (FAR.fromCodes [7,8,11,19,14,0,2,13,23,24,15,2]) := cover true B
#print axioms cover354
#print axioms cover355
end BB6.Agent6D1TwoUnary
