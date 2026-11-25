import CarryAperiodic
import BatchCarry
namespace BB6.Agent43CarryAperiodic
open BB6.Agent9BatchCarry

def carryAt (q c : Nat) : List Bool → Nat → Nat
  | [], _ => c
  | _::_, 0 => c
  | b::bs, j+1 => carryAt (q+1) ((c+(if b then q else 0))/2) bs j

def bitAt (xs : List Bool) (j : Nat) : Int := if xs[j]?.getD false then 1 else 0

/-- The same weight equality used by the original modular checker gives a
    carry history for the specified word, not just an existential path. -/
theorem carryAt_legal (q c : Nat) (xs : List Bool) (a : Nat)
    (hi : Interior q c) (he : c+weightSum q xs=2^xs.length*a) :
    (∀ j≤xs.length, Interior (q+j) (carryAt q c xs j)) ∧
    (∀ j<xs.length, 2*(carryAt q c xs (j+1):Int) =
      (carryAt q c xs j:Int)+((q:Int)+(j:Int))*bitAt xs j) := by
  induction xs generalizing q c with
  | nil =>
    constructor
    · intro j hj
      have : j=0 := by simpa using hj
      subst j
      simpa [carryAt] using hi
    · simp
  | cons b bs ih =>
    let v := if b then q else 0
    let z := (c+v)/2
    have hs : c+v+2*weightSum (q+1) bs=2*(2^bs.length*a) := by
      simp only [weightSum,List.length_cons,Nat.pow_succ] at he
      calc
        _ = c+((if b then q else 0)+2*weightSum (q+1) bs) := by simp [v,Nat.add_assoc]
        _ = (2^bs.length*2)*a := he
        _ = _ := by ac_rfl
    have hz : 2*z=c+v := by dsimp [z]; omega
    have he' : z+weightSum (q+1) bs=2^bs.length*a := by omega
    have hv : v=0 ∨ v=q := by cases b <;> simp [v]
    have hi' : Interior (q+1) z := by
      unfold Interior at hi ⊢
      rcases hv with h|h <;> omega
    obtain ⟨hbound,hstep⟩ := ih (q+1) z hi' he'
    constructor
    · intro j hj
      cases j with
      | zero => simpa [carryAt] using hi
      | succ j =>
        have h := hbound j (by simp at hj; omega)
        simpa only [carryAt,z,v,show q+(j+1)=q+1+j by omega] using h
    · intro j hj
      cases j with
      | zero =>
        have hzero : carryAt (q+1) z bs 0=z := by cases bs <;> rfl
        change 2*(carryAt (q+1) z bs 0:Int) = (c:Int)+((q:Int)+0)*bitAt (b::bs) 0
        rw [hzero]
        cases b <;> simp [bitAt,v] at hz ⊢ <;> omega
      | succ j =>
        have h := hstep j (by simp at hj; omega)
        simpa only [carryAt,z,v,bitAt,List.getElem?_cons_succ,Int.natCast_succ,Int.natCast_add,Int.natCast_one,show (q:Int)+1+(j:Int)=(q:Int)+((j:Int)+1) by omega] using h

theorem no_periodic_weight (q c p L a : Nat) (xs : List Bool)
    (hi : Interior q c) (hp : 0<p) (hlen : xs.length=2*p+L)
    (hperiod : ∀ j, j+p<xs.length → xs[j+p]?=xs[j]?)
    (hscale : 2*(q+p)<2^L) : c+weightSum q xs≠2^xs.length*a := by
  intro he
  obtain ⟨hbound,hstep⟩ := carryAt_legal q c xs a hi he
  apply no_long_period q p L (fun j => (carryAt q c xs j:Int)) (bitAt xs) hp
  · intro j hj
    have h := hbound j (by omega)
    unfold Interior at h
    omega
  · intro j _
    unfold bitAt
    split <;> simp
  · intro j hj
    exact hstep j (by omega)
  · intro j hj
    unfold bitAt
    rw [hperiod j (by omega)]
  · exact hscale

#print axioms carryAt_legal
#print axioms no_periodic_weight
end BB6.Agent43CarryAperiodic
