import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFZeroMarker
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
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

abbrev B := Q 1
abbrev E := Q 4
abbrev Z (n : Nat) := List.replicate n false

theorem zmerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem eSweep (n : Nat) (L R : List Bool) :
    run0 table n (E (false::L) (Z n++R)) = some (E (false::(U n++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (E (false::L) (Z (n+1)++R)) = some (E (false::true::L) (Z n++R)) := by rfl
    have H := join0 h (ih (true::L))
    have he : U n++true::L=U (n+1)++L := by
      change U n++(U 1++L)=_
      rw [umerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H

theorem bSweep (n : Nat) (L R : List Bool) :
    run0 table n (B (U n++L) R) = some (B L (Z n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (B (U (n+1)++L) R) = some (B (U n++L) (false::R)) := by rfl
    have H := join0 h (ih (false::R))
    have he : Z n++false::R=Z (n+1)++R := by
      change Z n++(Z 1++R)=_
      rw [zmerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H

def mark (k m : Nat) := F [false] (false::true::(Z (4*k+2)++S (2*m+1) []))

theorem start (k m : Nat) : Reach table (mark k m) (E (U (4*k+4)++[false,false]) (false::S (2*m) [])) := by
  have h1 : run0 table 3 (mark k m) = some (E [false,true,false,false] (Z (4*k+1)++S (2*m+1) [])) := by rfl
  have h2 := eSweep (4*k+1) [true,false,false] (S (2*m+1) [])
  have h3 : run0 table 1 (E (false::(U (4*k+1)++[true,false,false])) (S (2*m+1) [])) = some (E (true::true::(U (4*k+1)++[true,false,false])) (false::S (2*m) [])) := by rfl
  have H := join0 (join0 h1 h2) h3
  have he : U (4*k+1)++[true,false,false]=U (4*k+2)++[false,false] := by
    change U (4*k+1)++(U 1++[false,false])=_
    rw [umerge]
  rw [he] at H
  exact ⟨_,H⟩

theorem march (k m : Nat) : Reach table (mark k (m+1)) (mark (k+1) m) := by
  have h1 := start k (m+1)
  have h2 : run0 table 2 (E (U (4*k+4)++[false,false]) (false::S (2*(m+1)) [])) = some (B (U (4*k+6)++[false,false]) (false::S (2*m+1) [])) := by rfl
  have h3 := bSweep (4*k+6) [false,false] (false::S (2*m+1) [])
  have h4 : run0 table 9 (B [false,false] (Z (4*k+6)++false::S (2*m+1) [])) = some (F [false] (false::true::(Z (4*k+6)++S (2*m+1) []))) := by
    have he : Z (4*k+6)++false::S (2*m+1) []=false::false::(Z (4*k+4)++false::S (2*m+1) []) := by rfl
    rw [he]
    have hr : run0 table 9 (B [false,false] (false::false::(Z (4*k+4)++false::S (2*m+1) []))) = some (F [false] (false::true::false::(Z (4*k+4)++false::S (2*m+1) []))) := by rfl
    have he2 : Z (4*k+4)++false::S (2*m+1) []=Z (4*k+5)++S (2*m+1) [] := by
      change Z (4*k+4)++(Z 1++S (2*m+1) [])=_
      rw [zmerge]
    rw [he2] at hr
    rw [he2]
    exact hr
  have he : 4*(k+1)+2=4*k+6 := by omega
  unfold mark
  rw [he]
  exact reachTrans h1 (reachTrans ⟨2,h2⟩ (reachTrans ⟨_,h3⟩ ⟨9,h4⟩))

theorem finish (k : Nat) : ∃ t, 0<t ∧ run0 table t (mark k 0) = some (F [] (false::true::false::false::S (2*k+3) [])) := by
  obtain ⟨a,h1⟩ := start k 0
  have h2 : run0 table 8 (E (U (4*k+4)++[false,false]) [false]) = some (A (U (4*k+8)++[false,false]) []) := by rfl
  have h3 := aSweep (2*k+4) [false,false] []
  have h4 : run0 table 12 (A [false,false] (S (2*k+4) [])) = some (F [] (false::true::false::false::S (2*k+3) [])) := by rfl
  have he : 2*(2*k+4)=4*k+8 := by omega
  rw [he] at h3
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem walk (m k : Nat) : Reach table (mark k m) (mark (k+m) 0) := by
  induction m generalizing k with
  | zero => exact ⟨0,by rfl⟩
  | succ m ih =>
    have h1 := march k m
    have h2 := ih (k+1)
    rw [show k+1+m=k+(m+1) by omega] at h2
    exact reachTrans h1 h2

def family (n : Nat) := F [] (false::true::false::false::S (2*n+1) [])
theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem firstEq (R : List Bool) : step0 table (F [] R)=step0 table (F [false] R) := by rfl

theorem transfer (R : List Bool) (t : Nat) (h : 0<t) (c : Z0)
    (hr : run0 table t (F [false] R)=some c) : run0 table t (F [] R)=some c := by
  cases t with
  | zero => omega
  | succ t => simpa only [run0,firstEq] using hr

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨a,ha⟩ := walk n 0
  obtain ⟨b,hpos,hb⟩ := finish n
  simp only [Nat.zero_add] at ha
  have H := join0 ha hb
  exact ⟨a+b,by omega,transfer _ _ (by omega) _ H⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFZeroMarker
