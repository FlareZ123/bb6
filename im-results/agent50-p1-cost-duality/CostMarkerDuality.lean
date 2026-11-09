import CostDualityCore
namespace BB6.Agent50Cost

def bitVal (b : Bool) : Nat := if b then 1 else 0

def mask : List Bool → Nat
  | [] => 0
  | b :: bs => bitVal b + 2 * mask bs

def weight : Nat → Nat
  | 0 => 4
  | k+1 => 2^k * (k+9)

def weightedFrom (i : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then weight i else 0) + weightedFrom (i+1) bs

def weights (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => weight i + weights (i+1) n

def marker (bs : List Bool) : Nat := 2^bs.length + mask bs

def markerScore (bs : List Bool) : Nat := weight bs.length + weightedFrom 0 bs

theorem mask_complement (bs : List Bool) :
    mask bs + mask (bs.map (!·)) + 1 = 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [mask, bitVal, Nat.pow_succ] <;> omega

theorem weighted_complement (i : Nat) (bs : List Bool) :
    weightedFrom i bs + weightedFrom i (bs.map (!·)) = weights i bs.length := by
  induction bs generalizing i with
  | nil => simp [weightedFrom, weights]
  | cons b bs ih =>
    cases b <;> simp [weightedFrom, weights, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem weights_succ_right (i n : Nat) :
    weights i (n+1) = weights i n + weight (i+n) := by
  induction n generalizing i with
  | zero => simp [weights]
  | succ n ih =>
    change weight i + weights (i+1) (n+1) =
      (weight i + weights (i+1) n) + weight (i+(n+1))
    rw [ih (i+1)]
    have he : i+1+n = i+(n+1) := by omega
    rw [he]
    omega

-- At the first positive precision h, the weighted prefix sum has a closed form.
theorem weights_closed (h : Nat) (hh : 1 ≤ h) :
    weights 0 h + 3 = (h+6)*2^(h-1) := by
  induction h with
  | zero => omega
  | succ h ih =>
    cases h with
    | zero => decide
    | succ k =>
      change weights 0 (k+2) + 3 = (k+8)*2^(k+1)
      have hi : weights 0 (k+1) + 3 = (k+7)*2^k := by
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right,
          Nat.add_zero, Nat.zero_add] using (ih (by omega))
      have hs : weights 0 (k+2) = weights 0 (k+1) + weight (k+1) := by
        simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (weights_succ_right 0 (k+1))
      have hw : weight (k+1) = (k+9)*2^k := by
        simp [weight, Nat.mul_comm]
      have he : (k+7)*2^k + (k+9)*2^k = (k+8)*2^(k+1) := by
        rw [Nat.pow_succ]
        calc
          _ = ((k+7)+(k+9))*2^k := (Nat.add_mul (k+7) (k+9) (2^k)).symm
          _ = (2*(k+8))*2^k := by congr 1; omega
          _ = (k+8)*(2^k*2) := by ac_rfl
      rw [hs, hw]
      omega

theorem marker_complement (bs : List Bool) :
    marker bs + marker (bs.map (!·)) + 1 = 3*2^bs.length := by
  have hm := mask_complement bs
  simp only [marker, List.length_map]
  omega

theorem markerScore_complement (bs : List Bool) (h : 1 ≤ bs.length) :
    markerScore bs + markerScore (bs.map (!·)) + 3 =
      (3*bs.length+22)*2^(bs.length-1) := by
  have hw := weighted_complement 0 bs
  have hc := weights_closed bs.length h
  simp only [markerScore, List.length_map]
  have hi : weight bs.length = 2^(bs.length-1)*(bs.length+8) := by
    cases hv : bs.length with
    | zero => simp [hv] at h
    | succ k => simp [weight, hv, Nat.mul_comm]
  rw [hi]
  have he : 2*(2^(bs.length-1)*(bs.length+8)) +
        (bs.length+6)*2^(bs.length-1) =
        (3*bs.length+22)*2^(bs.length-1) := by
    calc
      _ = ((bs.length+6)+2*(bs.length+8))*2^(bs.length-1) := by
        rw [Nat.add_mul (bs.length+6) (2*(bs.length+8)) (2^(bs.length-1))]
        ac_rfl
      _ = (3*bs.length+22)*2^(bs.length-1) := by
        congr 1
        omega
  omega

theorem cost_congruence_duality (bs : List Bool) (q : Nat)
    (hh : 1 ≤ bs.length) :
    (2^bs.length ∣ (3+8*marker bs)*q+1+markerScore bs) ↔
    (2^bs.length ∣
      (5+8*marker (bs.map (!·)))*
         (q+shift (3*bs.length+22) (2^(bs.length-1)))+
       2+markerScore (bs.map (!·))) := by
  apply algebraic_duality
  · cases hv : bs.length with
    | zero => simp [hv] at hh
    | succ k => simp [hv, Nat.pow_succ, Nat.mul_comm]
  · exact marker_complement bs
  · exact markerScore_complement bs hh

#print axioms mask_complement
#print axioms weighted_complement
#print axioms weights_succ_right
#print axioms weights_closed
#print axioms marker_complement
#print axioms markerScore_complement
#print axioms cost_congruence_duality
end BB6.Agent50Cost
