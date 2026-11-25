import Raw60LFUnaryCore

namespace BB6.Agent1Raw60LFMarker

open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore

set_option maxRecDepth 4000

set_option maxHeartbeats 4000000

namespace Leaf233

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev anchor : List Bool := [false]

abbrev A := Q 0
abbrev D := Q 3

def P (a b : Bool) : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => a::b::P a b n R
abbrev T := P false true
abbrev S := P true false

theorem pairEnd (a b : Bool) (n : Nat) (R : List Bool) :
    P a b n (a::b::R)=P a b (n+1) R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,ih]

theorem umerge (a b : Nat) (L : List Bool) : U a++(U b++L)=U (a+b)++L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem dSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (D (true::L) (T n R)) = some (D (U (2*n)++true::L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (D (true::L) (T (n+1) R)) = some (D (true::true::true::L) (T n R)) := by rfl
    have h2 := ih (true::true::L)
    have H := join0 h h2
    rw [show 2+2*n=2*(n+1) by omega] at H
    have he : U (2*n)++true::true::true::L=U (2*(n+1))++true::L := by
      change U (2*n)++(U 2++true::L)=_
      rw [umerge,show 2*n+2=2*(n+1) by omega]
    rw [he] at H
    exact H

theorem leftSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (F (U (2*n)++L) R) = some (F L (T n R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (F (U (2*(n+1))++L) R) = some (F (U (2*n)++L) (false::true::R)) := by rfl
    have H := join0 h (ih (false::true::R))
    have he : T n (false::true::R)=T (n+1) R := pairEnd false true n R
    rw [he,show 2+2*n=2*(n+1) by omega] at H
    exact H

theorem aSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (A (U (2*n)++L) R) = some (A L (S n R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (A (U (2*(n+1))++L) R) = some (A (U (2*n)++L) (true::false::R)) := by rfl
    have H := join0 h (ih (true::false::R))
    have he : S n (true::false::R)=S (n+1) R := pairEnd true false n R
    rw [he,show 2+2*n=2*(n+1) by omega] at H
    exact H

def mark (k m : Nat) := F anchor (T (k+1) (false::false::S m []))

theorem start (k : Nat) (R : List Bool) :
    run0 table 2 (F anchor (T (k+1) R)) = some (D (true::true::anchor) (T (k) R)) := by rfl

theorem march (k m : Nat) : Reach table (mark k (m+1)) (mark (k+1) m) := by
  have h1 := start k (false::false::S (m+1) [])
  have h2 := dSweep (k) (true::anchor) (false::false::S (m+1) [])
  have he : U (2*(k))++true::true::anchor=U (2*(k)+2)++anchor := by
    change U (2*(k))++(U 2++anchor)=_
    rw [umerge]
  rw [he] at h2
  have h3 : run0 table 6 (D (U (2*(k)+2)++anchor) (false::false::S (m+1) [])) =
      some (F (U (2*(k)+4)++anchor) (false::false::S m [])) := by rfl
  have h4 := leftSweep (k+2) anchor (false::false::S m [])
  exact ⟨_,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem finish (k : Nat) : ∃ t, 0<t ∧ run0 table t (mark k 0) = some (F [] (T 1 (false::false::S (k+3) []))) := by
  have h1 := start k [false,false]
  have h2 := dSweep (k) (true::anchor) [false,false]
  have he : U (2*(k))++true::true::anchor=U (2*(k)+2)++anchor := by
    change U (2*(k))++(U 2++anchor)=_
    rw [umerge]
  rw [he] at h2
  have h3 : run0 table 12 (D (U (2*(k)+2)++anchor) [false,false]) = some (A (U (2*(k)+8)++anchor) []) := by rfl
  have h4 := aSweep (k+4) anchor []
  have h5 : run0 table 12 (A anchor (S (k+4) [])) = some (F [] (T 1 (false::false::S (k+3) []))) := by rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem walk (m k : Nat) : Reach table (mark k m) (mark (k+1*m) 0) := by
  induction m generalizing k with
  | zero => exact ⟨0,by rfl⟩
  | succ m ih =>
    have h1 := march k m
    have h2 := ih (k+1)
    rw [show k+1+1*m=k+1*(m+1) by omega] at h2
    exact reachTrans h1 h2

theorem firstEq (R : List Bool) : step0 table (F [] R)=step0 table (F anchor R) := by rfl

theorem transfer (R : List Bool) (t : Nat) (h : 0<t) (c : Z0)
    (hr : run0 table t (F anchor R)=some c) : run0 table t (F [] R)=some c := by
  cases t with
  | zero => omega
  | succ t => simpa only [run0,firstEq] using hr

def size : Nat → Nat
  | 0 => 1
  | n+1 => 1*size n+3
def family (n : Nat) := F [] (T 1 (false::false::S (size n) []))
theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨a,ha⟩ := walk (size n) 0
  obtain ⟨b,hpos,hb⟩ := finish (1*size n)
  simp only [Nat.zero_add] at ha
  have H := join0 ha hb
  have hp : 0<a+b := by omega
  exact ⟨a+b,hp,transfer _ _ hp _ H⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end Leaf233

namespace Leaf234

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev anchor : List Bool := []

abbrev A := Q 0
abbrev D := Q 3

def P (a b : Bool) : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => a::b::P a b n R
abbrev T := P false true
abbrev S := P true false

theorem pairEnd (a b : Bool) (n : Nat) (R : List Bool) :
    P a b n (a::b::R)=P a b (n+1) R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,ih]

theorem umerge (a b : Nat) (L : List Bool) : U a++(U b++L)=U (a+b)++L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem dSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (D (true::L) (T n R)) = some (D (U (2*n)++true::L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (D (true::L) (T (n+1) R)) = some (D (true::true::true::L) (T n R)) := by rfl
    have h2 := ih (true::true::L)
    have H := join0 h h2
    rw [show 2+2*n=2*(n+1) by omega] at H
    have he : U (2*n)++true::true::true::L=U (2*(n+1))++true::L := by
      change U (2*n)++(U 2++true::L)=_
      rw [umerge,show 2*n+2=2*(n+1) by omega]
    rw [he] at H
    exact H

theorem leftSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (F (U (2*n)++L) R) = some (F L (T n R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (F (U (2*(n+1))++L) R) = some (F (U (2*n)++L) (false::true::R)) := by rfl
    have H := join0 h (ih (false::true::R))
    have he : T n (false::true::R)=T (n+1) R := pairEnd false true n R
    rw [he,show 2+2*n=2*(n+1) by omega] at H
    exact H

theorem aSweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) (A (U (2*n)++L) R) = some (A L (S n R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (A (U (2*(n+1))++L) R) = some (A (U (2*n)++L) (true::false::R)) := by rfl
    have H := join0 h (ih (true::false::R))
    have he : S n (true::false::R)=S (n+1) R := pairEnd true false n R
    rw [he,show 2+2*n=2*(n+1) by omega] at H
    exact H

def mark (k m : Nat) := F anchor (T (k+1) (false::false::S m []))

theorem start (k : Nat) (R : List Bool) :
    run0 table 2 (F anchor (T (k+1) R)) = some (D (true::true::anchor) (T (k+1) R)) := by rfl

theorem march (k m : Nat) : Reach table (mark k (m+1)) (mark (k+2) m) := by
  have h1 := start k (false::false::S (m+1) [])
  have h2 := dSweep (k+1) (true::anchor) (false::false::S (m+1) [])
  have he : U (2*(k+1))++true::true::anchor=U (2*(k+1)+2)++anchor := by
    change U (2*(k+1))++(U 2++anchor)=_
    rw [umerge]
  rw [he] at h2
  have h3 : run0 table 6 (D (U (2*(k+1)+2)++anchor) (false::false::S (m+1) [])) =
      some (F (U (2*(k+1)+4)++anchor) (false::false::S m [])) := by rfl
  have h4 := leftSweep (k+3) anchor (false::false::S m [])
  exact ⟨_,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem finish (k : Nat) : ∃ t, 0<t ∧ run0 table t (mark k 0) = some (F [] (T 1 (false::false::S (k+4) []))) := by
  have h1 := start k [false,false]
  have h2 := dSweep (k+1) (true::anchor) [false,false]
  have he : U (2*(k+1))++true::true::anchor=U (2*(k+1)+2)++anchor := by
    change U (2*(k+1))++(U 2++anchor)=_
    rw [umerge]
  rw [he] at h2
  have h3 : run0 table 12 (D (U (2*(k+1)+2)++anchor) [false,false]) = some (A (U (2*(k+1)+8)++anchor) []) := by rfl
  have h4 := aSweep (k+5) anchor []
  have h5 : run0 table 12 (A anchor (S (k+5) [])) = some (F [] (T 1 (false::false::S (k+4) []))) := by rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem walk (m k : Nat) : Reach table (mark k m) (mark (k+2*m) 0) := by
  induction m generalizing k with
  | zero => exact ⟨0,by rfl⟩
  | succ m ih =>
    have h1 := march k m
    have h2 := ih (k+2)
    rw [show k+2+2*m=k+2*(m+1) by omega] at h2
    exact reachTrans h1 h2

def size : Nat → Nat
  | 0 => 1
  | n+1 => 2*size n+4
def family (n : Nat) := F [] (T 1 (false::false::S (size n) []))
theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨a,ha⟩ := walk (size n) 0
  obtain ⟨b,hpos,hb⟩ := finish (2*size n)
  simp only [Nat.zero_add] at ha
  have H := join0 ha hb
  have hp : 0<a+b := by omega
  exact ⟨a+b,hp,H⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end Leaf234

end BB6.Agent1Raw60LFMarker
