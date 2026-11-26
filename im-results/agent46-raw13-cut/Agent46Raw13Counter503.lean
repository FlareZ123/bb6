import Agent46AutoPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent46Counter503
open BB6Coverage Agent31Pump

def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def p2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none

/-- Little-endian binary increment with extension at overflow. -/
def inc : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::inc bs

theorem inc_ne_nil (bs : List Bool) : inc bs ≠ [] := by
  cases bs with
  | nil => decide
  | cons b bs => cases b <;> simp [inc]

def enc1 : List Bool → List Bool
  | [] => []
  | b::bs => false::b::enc1 bs

def enc2 : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b::c::bs => b::false::enc2 (c::bs)

def cost1 : List Bool → Nat
  | [] => 3
  | false::_ => 3
  | true::bs => 12 + cost1 bs

def E1 (L : List Bool) (bs : List Bool) : Z0 := ⟨4,false::L,(enc1 bs).tail⟩
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩

theorem pop1 (L R : List Bool) : run0 p1 5 (B (false::L) (false::R)) = some (B L (false::false::R)) := by rfl

theorem carry1 (L : List Bool) (bs : List Bool) :
    run0 p1 2 (E1 L (true::bs)) = some (E1 (false::false::L) bs) := by
  cases bs <;> rfl

theorem carry1_all (bs L : List Bool) :
    run0 p1 (cost1 bs) (E1 L bs) = some (B L (enc1 (inc bs))) := by
  induction bs generalizing L with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => rfl
    | true =>
      have h := join0 (carry1 L bs) (ih (false::false::L))
      cases hinc : inc bs with
      | nil => exact False.elim (inc_ne_nil bs hinc)
      | cons c cs =>
        rw [hinc] at h
        change run0 p1 (2+cost1 bs) (E1 L (true::bs)) = some (B (false::false::L) (false::c::enc1 cs)) at h
        have h' := join0 (join0 h (pop1 (false::L) (c::enc1 cs))) (pop1 L (false::c::enc1 cs))
        rw [show cost1 (true::bs) = 2+cost1 bs+5+5 by simp [cost1]; omega]
        simpa [inc,enc1,hinc] using h'

def iter : Nat → List Bool → List Bool
  | 0, bs => bs
  | n+1, bs => inc (iter n bs)

theorem step1 (bs : List Bool) : run0 p1 (1+cost1 bs) (B [true] (enc1 bs)) =
    some (B [true] (enc1 (inc bs))) := by
  have h : run0 p1 1 (B [true] (enc1 bs)) = some (E1 [true] bs) := by
    cases bs <;> rfl
  exact join0 h (carry1_all bs [true])

theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := by
  apply never_of_growth p1 (fun n => B [true] (enc1 (iter n [false]))) 6
    (fun n => 1 + cost1 (iter n [false]))
  · rfl
  · intro n; omega
  · intro n; exact step1 (iter n [false])
  · exact hm

-- In the second encoding the most-significant bit has no trailing separator.
def E2raw (k : Nat) (b : Bool) (R : List Bool) : Z0 :=
  ⟨4,b::(rep [false,false] k ++ [true,true]),R⟩
def E2 (k : Nat) (bs : List Bool) : Z0 :=
  E2raw k ((enc2 bs).headD false) (enc2 bs).tail

theorem pop2pair (L R : List Bool) : run0 p2 10 (B (false::false::L) (false::R)) =
    some (B L (false::false::false::R)) := by rfl

theorem rep00_comm (k : Nat) (R : List Bool) :
    rep [false,false] k ++ false::R = false::(rep [false,false] k ++ R) := by
  induction k <;> simp [rep, *]

theorem pop2pairs (k : Nat) (L R : List Bool) :
    run0 p2 (10*k) (B (rep [false,false] k ++ L) (false::R)) =
    some (B L (false::(rep [false,false] k ++ R))) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (pop2pair (rep [false,false] k ++ L) R) (ih (false::false::R))
    rw [show 10*(k+1)=10+10*k by omega]
    simpa only [rep,List.cons_append,List.nil_append,List.append_assoc,rep00_comm] using h

def stopCost2 : Nat → Nat
  | 0 => 5
  | k+1 => 7+10*k

theorem stop2 (k : Nat) (R : List Bool) :
    run0 p2 (stopCost2 k) (E2raw k false R) =
    some (B [true,true] (rep [false,false] k ++ true::R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : run0 p2 7 (E2raw (k+1) false R) =
        some (B (rep [false,false] k ++ [true,true]) (false::false::true::R)) := by rfl
    have h' := join0 h (pop2pairs k [true,true] (false::true::R))
    change run0 p2 (7+10*k) (E2raw (k+1) false R) = _
    simpa only [rep,List.cons_append,List.nil_append,List.append_assoc,rep00_comm] using h'

def carryCost2 (k : Nat) : List Bool → Nat
  | [] => stopCost2 k
  | false::_ => stopCost2 k
  | true::bs => 2+carryCost2 (k+1) bs

theorem advance2 (k : Nat) (bs : List Bool) :
    run0 p2 2 (E2 k (true::bs)) = some (E2 (k+1) bs) := by
  cases bs with
  | nil => rfl
  | cons b bs => cases bs <;> rfl

theorem carry2_all (bs : List Bool) (k : Nat) :
    run0 p2 (carryCost2 k bs) (E2 k bs) =
    some (B [true,true] (rep [false,false] k ++ enc2 (inc bs))) := by
  induction bs generalizing k with
  | nil => exact stop2 k []
  | cons b bs ih =>
    cases b with
    | false =>
      cases bs with
      | nil => exact stop2 k []
      | cons b bs => exact stop2 k (false::enc2 (b::bs))
    | true =>
      have h := join0 (advance2 k bs) (ih (k+1))
      cases hc : inc bs with
      | nil => exact False.elim (inc_ne_nil bs hc)
      | cons c cs =>
        rw [hc] at h
        change run0 p2 (2+carryCost2 (k+1) bs) (E2 k (true::bs)) = _
        simp only [inc,hc,enc2]
        simpa only [rep,List.cons_append,List.nil_append,List.append_assoc,rep00_comm] using h

theorem step2 (bs : List Bool) : run0 p2 (1+carryCost2 0 bs) (B [true,true] (enc2 bs)) =
    some (B [true,true] (enc2 (inc bs))) := by
  have h : run0 p2 1 (B [true,true] (enc2 bs)) = some (E2 0 bs) := by rfl
  exact join0 h (carry2_all bs 0)

theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := by
  apply never_of_growth p2 (fun n => B [true,true] (enc2 (iter n [false,true]))) 32
    (fun n => 1 + carryCost2 0 (iter n [false,true]))
  · rfl
  · intro n; omega
  · intro n; exact step2 (iter n [false,true])
  · exact hm

#print axioms never2
#print axioms carry1_all
#print axioms never1
#print axioms carry2_all
end BB6Coverage.Agent46Counter503
