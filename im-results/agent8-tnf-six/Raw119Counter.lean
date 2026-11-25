import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw119Counter
open BB6Coverage BB6Coverage.Agent31Pump
inductive Variant where | plain | bounce | erase

def extra : Variant → Nat | .erase => 4 | _ => 0

def table (v : Variant) (a1 : Option (Option Move)) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => a1
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with | .plain => none | _ => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .plain => some (some ⟨true,false,2⟩) | _ => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨(match v with | .erase => false | _ => true),true,0⟩)
  | _,_ => none
abbrev Z (n : Nat) := List.replicate n false
abbrev O (n : Nat) := List.replicate n true
def E (k : Nat) (L R : List Bool) : Z0 := ⟨4,Z (6+k) ++ [true,false] ++ L,R⟩
def F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def H (k : Nat) (L R : List Bool) : Z0 := ⟨4,true::(Z (5+k) ++ [true,false] ++ L),R⟩

theorem fSweep (v : Variant) (a : Option (Option Move)) (n : Nat) (L R : List Bool) :
    run0 (table v a) n (F (Z n ++ L) R) = some (F L (Z n ++ R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    change run0 (table v a) n (F (Z n ++ L) (false::R)) = _
    rw [ih]
    congr 2
    change List.replicate n false ++ ([false]++R) = List.replicate (n+1) false ++ R
    rw [List.replicate_succ', List.append_assoc]

theorem frontBase (v : Variant) (a : Option (Option Move)) (L R : List Bool) :
    run0 (table v a) (28+extra v) (F ([true,false]++L) ([false,false,false,false,false,true]++R)) = some (H 0 L R) := by cases v <;> rfl
theorem frontReset (v : Variant) (a : Option (Option Move)) (L R : List Bool) :
    run0 (table v a) (28+extra v) (F ([true,false]++L) ([false,false,false,false,false,false]++R)) = some (E 0 L R) := by cases v <;> rfl

theorem firstBase (v : Variant) (a : Option (Option Move)) (L R : List Bool) :
    run0 (table v a) 1 (E 0 L R) = some (F (Z 5 ++ [true,false]++L) (true::R)) := by rfl
theorem firstReset (v : Variant) (a : Option (Option Move)) (k : Nat) (L R : List Bool) :
    run0 (table v a) 1 (E (k+1) L R) = some (F (Z (6+k) ++ [true,false]++L) (true::R)) := by rfl

theorem reset (v : Variant) (a : Option (Option Move)) (k : Nat) (L R : List Bool) :
    run0 (table v a) (1+(6+k)+(28+extra v)) (E (k+1) L R) = some (E 0 L (Z k ++ true::R)) := by
  have h1 := firstReset v a k L R
  have h2 := fSweep v a (6+k) ([true,false]++L) (true::R)
  have h3 := frontReset v a L (Z k ++ true::R)
  rw [show Z (6+k) ++ true::R = [false,false,false,false,false,false]++(Z k ++ true::R) by
    change List.replicate (6+k) false ++ true::R = _
    rw [← List.replicate_append_replicate (n := 6) (m := k) (a := false), List.append_assoc]; rfl] at h2
  rw [List.append_assoc] at h1
  exact join0 (join0 h1 h2) h3

theorem baseFront (v : Variant) (a : Option (Option Move)) (L R : List Bool) :
    run0 (table v a) (1+5+(28+extra v)) (E 0 L R) = some (H 0 L R) := by
  have h1 := firstBase v a L R
  have h2 := fSweep v a 5 ([true,false]++L) (true::R)
  have h3 := frontBase v a L R
  rw [List.append_assoc] at h1
  exact join0 (join0 h1 h2) h3

theorem hStep (v : Variant) (a : Option (Option Move)) (k : Nat) (L R : List Bool) :
    run0 (table v a) 1 (H k L (true::R)) = some (H (k+1) L R) := by rfl

theorem hSweep (v : Variant) (a : Option (Option Move)) (j k : Nat) (L R : List Bool) :
    run0 (table v a) j (H k L (O j++R)) = some (H (k+j) L R) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    have h := join0 (hStep v a k L (O j++R)) (ih (k+1))
    rw [show 1+j=j+1 by omega,show k+1+j=k+(j+1) by omega] at h
    exact h

theorem hExit (v : Variant) (a : Option (Option Move)) (k : Nat) (L R : List Bool) (hR : R.headD false=false) :
    run0 (table v a) 1 (H k L R) = some (E (k+1) L R.tail) := by
  have hz : Z (6+(k+1)) = false::false::Z (5+k) := by
    rw [show 6+(k+1)=(5+k)+1+1 by omega]; rfl
  unfold E
  rw [hz]
  cases R with
  | nil => rfl
  | cons b R =>
    have hb : b=false := hR
    subst b
    rfl

theorem advanceBase (v : Variant) (a : Option (Option Move)) (j : Nat) (L R : List Bool) (hR : R.headD false=false) :
    run0 (table v a) (1+5+(28+extra v)+j+1) (E 0 L (O j++R)) = some (E (j+1) L R.tail) := by
  have h1 := baseFront v a L (O j++R)
  have h2 := hSweep v a j 0 L R
  have h3 := hExit v a j L R hR
  simp only [Nat.zero_add] at h2
  exact join0 (join0 h1 h2) h3

def costs (v : Variant) : Nat → Nat × (Nat → Nat)
  | 0 => (0, fun j => 1+5+(28+extra v)+j+1)
  | k+1 => ((costs v k).1 + (costs v k).2 0,
      fun j => (1+(6+k)+(28+extra v)) + (costs v k).1 + (costs v k).2 (j+1))

theorem countAdvance (v : Variant) (a : Option (Option Move)) (k : Nat) :
    (∀ L R, run0 (table v a) (costs v k).1 (E 0 L (Z k ++ R)) = some (E k L R)) ∧
    (∀ j L R, R.headD false=false →
      run0 (table v a) ((costs v k).2 j) (E k L (O j++R)) = some (E (k+j+1) L R.tail)) := by
  induction k with
  | zero =>
    constructor
    · intro L R; rfl
    · intro j L R hR; simpa only [costs,Nat.zero_add] using advanceBase v a j L R hR
  | succ k ih =>
    obtain ⟨hc,ha⟩ := ih
    constructor
    · intro L R
      have h1 := hc L (false::R)
      have h2 := ha 0 L (false::R) rfl
      have hz : Z k ++ false::R = Z (k+1) ++ R := by
        change List.replicate k false ++ ([false]++R) = List.replicate (k+1) false ++ R
        rw [List.replicate_succ',List.append_assoc]
      rw [hz] at h1
      exact join0 h1 h2
    · intro j L R hR
      have h1 := reset v a k L (O j++R)
      have h2 := hc L (O (j+1)++R)
      have h3 := ha (j+1) L R hR
      have h := join0 (join0 h1 h2) h3
      rw [show k+(j+1)+1=(k+1)+j+1 by omega] at h
      exact h

theorem growth (v : Variant) (a : Option (Option Move)) (k : Nat) (L : List Bool) :
    run0 (table v a) ((costs v k).2 0) (E k L []) = some (E (k+1) L []) := by
  exact (countAdvance v a k).2 0 L [] rfl

theorem advance_pos (v : Variant) (k j : Nat) : 0 < (costs v k).2 j := by
  cases k <;> simp [costs] <;> omega
#print axioms growth
end BB6.Agent8Raw119Counter
