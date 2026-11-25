import SweepPumping

namespace BB6.Agent10Raw107LF1655
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def pairs (b : Bool) : Nat → List Bool
  | 0 => []
  | n+1 => true :: b :: pairs b n

def enc : List Bool → List Bool
  | [] => []
  | b::bs => true :: b :: enc bs

def Z (k : Nat) : List Bool := false :: pairs false k ++ [true,true,true,true,false]
def O (k : Nat) : List Bool := true :: pairs false k ++ [true,true,true,true,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩

theorem pairs_snoc (b : Bool) (n : Nat) (R : List Bool) :
    pairs b n ++ true :: b :: R = pairs b (n+1) ++ R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true :: b :: (pairs b n ++ true :: b :: R) = true :: b :: (pairs b (n+1) ++ R)
    rw [ih]

theorem enc_append (a b : List Bool) : enc (a ++ b) = enc a ++ enc b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [enc,ih]

theorem enc_replicate (b : Bool) (n : Nat) : enc (List.replicate n b) = pairs b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,enc,pairs,ih]

theorem init (k : Nat) :
    run0 table 12 (A (Z k) []) = some (A (O (k+1)) [true]) := by rfl

theorem f_start (k : Nat) (R : List Bool) :
    run0 table 2 (A (O (k+1)) R) = some (F (Z k) (true::false::R)) := by rfl

theorem f_step (k : Nat) (R : List Bool) :
    run0 table 2 (F (Z (k+1)) R) = some (F (Z k) (true::true::R)) := by rfl

theorem f_scan (k : Nat) (R : List Bool) :
    run0 table (2*k) (F (Z k) R) = some (F (Z 0) (pairs true k ++ R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (f_step k R) (ih (true::true::R))
    rw [pairs_snoc] at h
    rw [show 2*(k+1) = 2+2*k by omega]
    exact h

theorem f_end (R : List Bool) :
    run0 table 22 (F (Z 0) R) = some (A (Z 0) R) := by rfl

theorem unwind (k : Nat) (R : List Bool) :
    run0 table (2+2*k+22) (A (O (k+1)) R) =
      some (A (Z 0) (pairs true k ++ true::false::R)) :=
  join0 (join0 (f_start k R) (f_scan k (true::false::R))) (f_end _)

theorem push_zero (k : Nat) (R : List Bool) :
    run0 table 4 (A (Z k) (true::false::R)) = some (A (Z (k+1)) R) := by rfl

theorem push_one (k : Nat) (R : List Bool) :
    run0 table 4 (A (Z k) (true::true::R)) = some (A (O (k+1)) R) := by rfl

theorem push_last (k : Nat) :
    run0 table 4 (A (Z k) [true]) = some (A (Z (k+1)) []) := by rfl

theorem push_zeros (n k : Nat) (R : List Bool) :
    run0 table (4*n) (A (Z k) (pairs false n ++ R)) = some (A (Z (k+n)) R) := by
  induction n generalizing k with
  | zero => simp [pairs,run0]
  | succ n ih =>
    have h := join0 (push_zero k (pairs false n ++ R)) (ih (k+1))
    rw [show 4*(n+1) = 4+4*n by omega, show k+(n+1) = k+1+n by omega]
    exact h

theorem decr (n : Nat) (R : List Bool) :
    ∃ t, run0 table t (A (Z 0) (pairs false n ++ true::true::R)) =
      some (A (Z 0) (pairs true n ++ true::false::R)) := by
  have h := push_zeros n 0 (true::true::R)
  simp only [Nat.zero_add] at h
  exact ⟨_, join0 (join0 h (push_one n R)) (unwind n R)⟩

-- bs is in most-significant-first order. The tape stores it in reverse order.
theorem clear (n : Nat) (bs : List Bool) (hlen : bs.length = n) (R : List Bool) :
    ∃ t, run0 table t (A (Z 0) (enc bs.reverse ++ R)) =
      some (A (Z 0) (pairs false n ++ R)) := by
  induction n generalizing bs R with
  | zero =>
    have h : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst bs
    exact ⟨0,rfl⟩
  | succ n ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs.length = n := by simpa using hlen
      obtain ⟨t,ht⟩ := ih bs hb (true::b::R)
      have hstart : enc (b::bs).reverse ++ R = enc bs.reverse ++ true::b::R := by
        simp [List.reverse_cons,enc_append,enc,List.append_assoc]
      rw [hstart]
      cases b with
      | false =>
        rw [pairs_snoc] at ht
        exact ⟨t,ht⟩
      | true =>
        obtain ⟨u,hu⟩ := decr n R
        obtain ⟨v,hv⟩ := ih (List.replicate n true) (by simp) (true::false::R)
        rw [List.reverse_replicate,enc_replicate,pairs_snoc] at hv
        exact ⟨_,join0 (join0 ht hu) hv⟩

theorem entry : run0 table 24 (A [] []) = some (A (Z 0) []) := by rfl

theorem epoch (k : Nat) : ∃ t, 0 < t ∧
    run0 table t (A (Z k) []) = some (A (Z (k+2)) []) := by
  have h1 := join0 (init k) (unwind k [true])
  obtain ⟨t,ht⟩ := clear (k+1) (false :: List.replicate k true) (by simp) [true]
  rw [List.reverse_cons,List.reverse_replicate,enc_append,enc_replicate] at ht
  simp only [enc,List.nil_append,List.cons_append,List.append_assoc] at ht
  have h2 := push_zeros (k+1) 0 [true]
  simp only [Nat.zero_add] at h2
  exact ⟨_,by omega,join0 (join0 (join0 h1 ht) h2) (push_last (k+1))⟩

def family (n : Nat) : Z0 := A (Z (2*n)) []

noncomputable def cost (n : Nat) : Nat := (epoch (2*n)).choose

theorem cost_pos (n : Nat) : 0 < cost n := (epoch (2*n)).choose_spec.1

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h := (epoch (2*n)).choose_spec.2
  change run0 table (cost n) (A (Z (2*n)) []) = some (A (Z (2*(n+1))) [])
  rw [show 2*(n+1)=2*n+2 by omega]
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 cost entry cost_pos growth m hm

#print axioms clear
#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw107LF1655
