import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFBitCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,v,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev C := Q 2
abbrev D := Q 3
abbrev Z (n : Nat) := List.replicate n false
abbrev P (L : List Bool) := true::true::false::true::true::false::false::L
def W (n s : Nat) := U (2*n+3)++false::true::true::true::true::false::U (s+1)

theorem zmerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]
theorem cSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n (C (true::L) (U n++R)) = some (C (true::(Z n++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (C (true::L) (U (n+1)++R)) = some (C (true::false::L) (U n++R)) := by cases v <;> rfl
    have H := join0 h (ih (false::L))
    have he : Z n++false::L=Z (n+1)++L := by
      change Z n++(Z 1++L)=_
      rw [zmerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H

theorem dSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n (D (Z n++L) R) = some (D L (U n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (D (Z (n+1)++L) R) = some (D (Z n++L) (true::R)) := by cases v <;> rfl
    have H := join0 h (ih (true::R))
    have he : U n++true::R=U (n+1)++R := by
      change U n++(U 1++R)=_
      rw [← List.append_assoc,List.replicate_append_replicate]
    rw [he,Nat.add_comm 1 n] at H
    exact H

def extra (v : Bool) := if v then 14 else 12

theorem zeroDigit (v : Bool) (n s : Nat) (L : List Bool) :
    ∃ t, 2≤t ∧ run0 (table v) t (F (false::false::L) (W n s)) = some (D (Z (s+5)++P (Z (2*n)++true::true::L)) []) := by
  have h1 : run0 (table v) 3 (F (false::false::L) (W n s)) = some (C (true::true::true::L) (U (2*n+2)++false::true::true::true::true::false::U (s+1))) := by cases v <;> rfl
  have h2 := cSweep v (2*n+2) (true::true::L) (false::true::true::true::true::false::U (s+1))
  have h3 : run0 (table v) 7 (C (true::(Z (2*n+2)++true::true::L)) (false::true::true::true::true::false::U (s+1))) = some (F (Z (2*n+4)++true::true::L) (true::true::false::true::false::U (s+1))) := by cases v <;> rfl
  have h4 : run0 (table v) (extra v) (F (Z (2*n+4)++true::true::L) (true::true::false::true::false::U (s+1))) = some (C (true::true::true::false::true::true::false::false::(Z (2*n)++true::true::L)) (U (s+2))) := by cases v <;> rfl
  have h5 := cSweep v (s+2) (true::true::false::true::true::false::false::(Z (2*n)++true::true::L)) []
  have h6 : run0 (table v) 2 (C (true::(Z (s+2)++true::true::false::true::true::false::false::(Z (2*n)++true::true::L))) []) = some (D (Z (s+5)++P (Z (2*n)++true::true::L)) []) := by cases v <;> rfl
  simp only [List.append_nil] at h5
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6⟩

theorem firstEq (v : Bool) (R : List Bool) : run0 (table v) 2 (F [] R)=run0 (table v) 2 (F [false,false] R) := by cases v <;> cases R <;> rfl

theorem transfer (v : Bool) (R : List Bool) (t : Nat) (h : 2≤t) (c : Z0)
    (hr : run0 (table v) t (F [false,false] R)=some c) : run0 (table v) t (F [] R)=some c := by
  have ht : t=2+(t-2) := by omega
  rw [ht,run0_add,firstEq,←run0_add,←ht]
  exact hr

def enc : List Bool → List Bool
  | [] => []
  | b::bs => b::b::enc bs

def next : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::next bs

theorem carry (v : Bool) (bs : List Bool) (n s : Nat) : Reach (table v) (F (enc bs) (W n s)) (D (Z (s+5)++P (Z (2*n)++enc (next bs))) []) := by
  induction bs generalizing n with
  | nil =>
    obtain ⟨t,ht,h⟩ := zeroDigit v n s []
    exact ⟨t,transfer v _ t ht _ h⟩
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨t,_,h⟩ := zeroDigit v n s (enc bs)
      exact ⟨t,h⟩
    | true =>
      have h1 : run0 (table v) 2 (F (enc (true::bs)) (W n s)) = some (F (enc bs) (W (n+1) s)) := by cases v <;> rfl
      have h2 := ih (n+1)
      have he : Z (2*(n+1))++enc (next bs)=Z (2*n)++enc (next (true::bs)) := by
        change Z (2*n+2)++enc (next bs)=Z (2*n)++(Z 2++enc (next bs))
        rw [zmerge]
      rw [he] at h2
      exact reachTrans ⟨2,h1⟩ h2

def bits : Nat → List Bool
  | 0 => [false,false,false,true]
  | n+1 => next (bits n)
def family (n : Nat) := D (Z (2*n+9)++P (enc (bits n))) []
def enterTime (v : Bool) := if v then 219 else 217

theorem entry (v : Bool) : run0 (table v) (enterTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth_exists (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family n) = some (family (n+1)) := by
  have h1 := dSweep v (2*n+9) (P (enc (bits n))) []
  simp only [List.append_nil] at h1
  have h2 : run0 (table v) 23 (D (P (enc (bits n))) (U (2*n+9))) = some (F (enc (bits n)) (W 0 (2*n+6))) := by cases v <;> rfl
  obtain ⟨t,h3⟩ := carry v (bits n) 0 (2*n+6)
  have he : 2*n+6+5=2*(n+1)+9 := by omega
  rw [he] at h3
  exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩
noncomputable def cost (v : Bool) (n : Nat) : Nat := Classical.choose (growth_exists v n)
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (enterTime v) (cost v) (entry v) (fun n => (Classical.choose_spec (growth_exists v n)).1)
    (fun n => (Classical.choose_spec (growth_exists v n)).2) m hm
namespace Leaf990
abbrev table := BB6.Agent1Raw60LFBitCounter.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFBitCounter.never false m hm
#print axioms never
end Leaf990
namespace Leaf992
abbrev table := BB6.Agent1Raw60LFBitCounter.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFBitCounter.never true m hm
#print axioms never
end Leaf992
end BB6.Agent1Raw60LFBitCounter
