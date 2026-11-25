import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw117Nested
open BB6Coverage BB6Coverage.Agent31Pump

-- false: A1=1LF (4216); true: A1=1LE (4215).
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,if v then 4 else 5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

theorem repeat_add (b : Bool) (n m : Nat) : List.replicate (n+m) b = List.replicate n b ++ List.replicate m b := by
  induction n with
  | zero => simp
  | succ n ih => rw [show n+1+m=n+m+1 by omega, List.replicate_succ, ih, List.replicate_succ]; rfl

def P (k : Nat) : List Bool := [false,false,false,true] ++ Z k ++ [true]
def A (L : List Bool) (m k : Nat) : Z0 := ⟨0,L,O m ++ P k⟩
def C (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,R.headD false::L,R.tail⟩

theorem bSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n ⟨1,true::L,O n ++ R⟩ = some ⟨1,true::(Z n ++ L),R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 ⟨1,true::L,O (n+1) ++ R⟩ = some ⟨1,true::false::L,O n ++ R⟩ := by rfl
    have g := join0 h (ih (false::L))
    rw [show 1+n=n+1 by omega] at g
    simpa only [O,Z,List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append] using g

theorem dSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (3*n) (C 3 (true::L) (Z n ++ R)) = some (C 3 (true::(O n ++ L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 3 (C 3 (true::L) (Z (n+1) ++ R)) = some (C 3 (true::true::L) (Z n ++ R)) := by rfl
    have g := join0 h (ih (true::L))
    rw [show 3+3*n=3*(n+1) by omega] at g
    simpa only [O,Z,List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append] using g

theorem fSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n ⟨5,O n ++ L,R⟩ = some ⟨5,L,Z n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 ⟨5,O (n+1) ++ L,R⟩ = some ⟨5,O n ++ L,false::R⟩ := by rfl
    have g := join0 h (ih (false::R))
    rw [show 1+n=n+1 by omega] at g
    simpa only [O,Z,List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append] using g

theorem first (v : Bool) (a k : Nat) (l L : List Bool)
    (hh : l.headD false = false) (ht : l.tail=L) :
    run0 (table v) (a+2+4*k+17) (A l (a+2) k) =
      some ⟨0,Z (a+1) ++ true::L,true::(Z (k+5) ++ [true])⟩ := by
  have h1 : run0 (table v) 1 (A l (a+2) k) = some ⟨1,true::true::L,O (a+1) ++ P k⟩ := by
    simp only [A,List.replicate_succ,List.cons_append,run0,step0,hh,ht,table,move0]
    rfl
  have h2 := bSweep v (a+1) (true::L) (P k)
  have h3 : run0 (table v) 9 ⟨1,true::(Z (a+1) ++ true::L),P k⟩ =
      some (C 3 (true::true::true::true::(Z (a+2) ++ true::L)) (Z k ++ [true])) := by
    rfl
  have h4 := dSweep v k (true::true::true::(Z (a+2) ++ true::L)) [true]
  have h5 : run0 (table v) 2 (C 3 (true::(O k ++ true::true::true::(Z (a+2) ++ true::L))) [true]) =
      some ⟨5,O (k+5) ++ (Z (a+2) ++ true::L),[true]⟩ := by
    unfold C O
    rw [show k+5=2+k+3 by omega,repeat_add true (2+k) 3,repeat_add true 2 k]
    simp only [List.append_assoc]
    rfl
  have h6 := fSweep v (k+5) (Z (a+2) ++ true::L) [true]
  have h7 : run0 (table v) 1 ⟨5,Z (a+2) ++ true::L,Z (k+5) ++ [true]⟩ =
      some ⟨0,Z (a+1) ++ true::L,true::(Z (k+5) ++ [true])⟩ := by rfl
  have g := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  rw [show 1+(a+1)+9+3*k+2+(k+5)+1=a+2+4*k+17 by omega] at g
  exact g

theorem second (v : Bool) (a k : Nat) (L : List Bool) :
    run0 (table v) 14 ⟨0,Z (a+1) ++ true::L,true::(Z (k+5) ++ [true])⟩ =
      some (A (true::(Z a ++ true::L)) 1 (k+1)) := by
  unfold A P O Z
  rfl

theorem Q (v : Bool) (a k : Nat) (l L : List Bool)
    (hh : l.headD false = false) (ht : l.tail=L) :
    run0 (table v) (a+2+4*k+31) (A l (a+2) k) =
      some (A (true::(Z a ++ true::L)) 1 (k+1)) := by
  have h := join0 (first v a k l L hh ht) (second v a k L)
  rw [show a+2+4*k+17+14=a+2+4*k+31 by omega] at h
  exact h

/-- A positive-length exact return. The witness need not be a closed-form cost. -/
def Reach (v : Bool) (a b : Z0) : Prop :=
  ∃ t : Nat, 0<t ∧ run0 (table v) t a = some b

theorem reachJoin {v : Bool} {a b c : Z0} (h : Reach v a b) (g : Reach v b c) : Reach v a c := by
  obtain ⟨t,ht,h⟩ := h
  obtain ⟨u,hu,g⟩ := g
  exact ⟨t+u,by omega,join0 h g⟩

def d (v : Bool) : Nat := if v then 3 else 2
def m (v : Bool) (p : Nat) : Nat := d v * (p+1)+1

theorem shift (v : Bool) (L R : List Bool) :
  run0 (table v) (d v) ⟨0,true::(Z (d v-1) ++ L),R⟩ = some ⟨0,L,O (d v) ++ R⟩ := by
  cases v <;> rfl

theorem shiftA (v : Bool) (L : List Bool) (x k : Nat) :
    Reach v (A (true::(Z (d v-1) ++ L)) x k) (A L (d v+x) k) := by
  refine ⟨d v,by cases v <;> decide,?_⟩
  unfold A O
  rw [repeat_add true (d v) x,List.append_assoc]
  exact shift v L (O x ++ P k)

theorem setup (v : Bool) (p k : Nat) (l L : List Bool)
    (hh : l.headD false = false) (ht : l.tail=L) :
    Reach v (A l (m v p) k) (A (Z (d v*p) ++ true::L) (m v 0) (k+1)) := by
  have h := Q v (d v-1+d v*p) k l L hh ht
  have e : d v-1+d v*p+2=m v p := by cases v <;> simp [d,m] <;> omega
  rw [e] at h
  have w : Z (d v-1+d v*p) ++ true::L = Z (d v-1) ++ (Z (d v*p) ++ true::L) := by
    unfold Z
    rw [repeat_add,List.append_assoc]
  rw [w] at h
  have g := shiftA v (Z (d v*p) ++ true::L) 1 (k+1)
  have e0 : d v+1=m v 0 := by simp [m]
  rw [e0] at g
  exact reachJoin ⟨_,by omega,h⟩ g

/-- Nested return: processing the scanned zero preserves its untouched left
    tail, changes that zero to one, and adds exactly 2^p zeros to the gap. -/
theorem zeroReturn (v : Bool) (p : Nat) : ∀ k : Nat, ∀ l L : List Bool,
    l.headD false=false → l.tail=L →
    Reach v (A l (m v p) k) (A (true::L) (m v p) (k+2^p)) := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro k l L hh ht
    have hs := setup v p k l L hh ht
    have H : ∀ i ≤ p, Reach v (A l (m v p) k)
        (A (Z (d v*(p-i)) ++ true::L) (m v i) (k+2^i)) := by
      intro i hi
      induction i with
      | zero => simpa using hs
      | succ i step =>
        have hprev := step (by omega)
        let T := Z (d v*(p-(i+1))) ++ true::L
        have w : Z (d v*(p-i)) ++ true::L = false::(Z (d v-1) ++ T) := by
          have e : d v*(p-i)=1+(d v-1)+d v*(p-(i+1)) := by cases v <;> simp [d] <;> omega
          unfold T Z
          rw [e,repeat_add false (1+(d v-1)),repeat_add false 1]
          simp only [List.append_assoc]
          rfl
        rw [w] at hprev
        have hinner := ih i (by omega) (k+2^i) (false::(Z (d v-1) ++ T)) (Z (d v-1) ++ T) rfl rfl
        have hshift := shiftA v T (m v i) (k+2^i+2^i)
        have em : d v+m v i=m v (i+1) := by cases v <;> simp [d,m] <;> omega
        have ek : k+2^i+2^i=k+2^(i+1) := by rw [Nat.pow_succ]; omega
        rw [ek] at hinner
        rw [em,ek] at hshift
        exact reachJoin (reachJoin hprev hinner) hshift
    simpa using H p (Nat.le_refl p)

theorem blankShift (v : Bool) (x k : Nat) :
    Reach v (A [true] x k) (A [] (d v+x) k) := by
  refine ⟨d v,by cases v <;> decide,?_⟩
  unfold A O
  rw [repeat_add true (d v) x,List.append_assoc]
  cases v <;> rfl

def family (v : Bool) (p : Nat) : Z0 := A [] (m v p) (2^p-1)

theorem entry (v : Bool) : run0 (table v) (if v then 31 else 30) ⟨0,[],[]⟩ = some (family v 0) := by
  cases v <;> rfl

theorem growth (v : Bool) (p : Nat) : Reach v (family v p) (family v (p+1)) := by
  have h := zeroReturn v p (2^p-1) [] [] rfl rfl
  have g := blankShift v (m v p) (2^p-1+2^p)
  have em : d v+m v p=m v (p+1) := by cases v <;> simp [d,m] <;> omega
  have ep : 0 < 2^p := Nat.pow_pos (by decide)
  have ek : 2^p-1+2^p=2^(p+1)-1 := by rw [Nat.pow_succ];omega
  rw [ek] at h
  rw [em,ek] at g
  exact reachJoin h g

noncomputable def cost (v : Bool) (p : Nat) : Nat := Classical.choose (growth v p)
theorem cost_pos (v : Bool) (p : Nat) : 0 < cost v p := (Classical.choose_spec (growth v p)).1
theorem cost_run (v : Bool) (p : Nat) : run0 (table v) (cost v p) (family v p) = some (family v (p+1)) := (Classical.choose_spec (growth v p)).2

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) (if v then 31 else 30) (cost v) (entry v) (cost_pos v) (cost_run v) m hm

#print axioms zeroReturn
#print axioms growth
#print axioms never
end BB6.Agent8Raw117Nested
