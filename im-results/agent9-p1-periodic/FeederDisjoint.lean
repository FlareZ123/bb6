import SourcePeriodAllPeriods

/-!
# Synchronous inverse-depth separation of the original P1 feeders

A common depth word for the genuine roots (16q+8,12q+4) and
(16q+9,10q+4) has binary marker equal to the low cost bits of 2q.
Consequently its total cost is uniformly bounded for fixed q. This
includes arbitrary aperiodic words and is a pairwise restriction only.
-/

namespace BB6.Agent9CrossFeeder
open PeriodWord

/-- Exact shared-word marker congruence for the two original feeder roots. -/
theorem same_q_feeder_marker (q : Nat) (w : List Nat)
    (m0 z0 m1 z1 : Nat)
    (h0 : Run (16*q+8) w 0 (12*q+4) m0 z0)
    (h1 : Run (16*q+9) w 0 (10*q+4) m1 z1) :
    weight w % 2^(cost w) = (2*q) % 2^(cost w) := by
  have ha0 := block_affine (16*q+8) w 0 (12*q+4) m0 z0 h0
  have ha1 := block_affine (16*q+9) w 0 (10*q+4) m1 z1 h1
  simp only [Int.natCast_add, Int.natCast_mul] at ha0 ha1
  have hdiff : ((2^(cost w):Nat):Int)*((z1:Int)-(z0:Int)) =
      (weight w:Int)-2*(q:Int) := by
    calc
      ((2^(cost w):Nat):Int)*((z1:Int)-(z0:Int)) =
          ((2^(cost w):Nat):Int)*(z1:Int) -
          ((2^(cost w):Nat):Int)*(z0:Int) := by simp [Int.mul_sub]
      _ = (weight w:Int)-2*(q:Int) := by
        rw [ha1,ha0]
        simp only [Int.mul_add]
        omega
  have hdvd : ((2^(cost w):Nat):Int) ∣
      ((weight w:Int)-(2*q:Nat)) := by
    refine ⟨(z1:Int)-(z0:Int), ?_⟩
    simpa [Int.natCast_mul] using hdiff.symm
  have hmodI : (weight w:Int) % ((2^(cost w):Nat):Int) =
      ((2*q:Nat):Int) % ((2^(cost w):Nat):Int) :=
    (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr
      (Int.emod_eq_zero_of_dvd hdvd)
  have heq : ((weight w % 2^(cost w):Nat):Int) =
      (((2*q) % 2^(cost w):Nat):Int) := by
    simpa [Int.natCast_emod] using hmodI
  exact_mod_cast heq

/-- Every nonempty depth word common to the two source feeder roots at the
same parameter q has total cost M satisfying 2^(M-1) ≤ 2q. -/
theorem same_q_feeder_cost_bound (q : Nat) (w : List Nat)
    (m0 z0 m1 z1 : Nat) (hne : w ≠ [])
    (h0 : Run (16*q+8) w 0 (12*q+4) m0 z0)
    (h1 : Run (16*q+9) w 0 (10*q+4) m1 z1) :
    2^(cost w-1) ≤ 2*q := by
  have hmarker := same_q_feeder_marker q w m0 z0 m1 z1 h0 h1
  have hsmall := PeriodWord.marker_bound w
  rw [Nat.mod_eq_of_lt hsmall] at hmarker
  have hlow := PeriodWord.weight_lower w hne
  have horder : 2^(cost w-1) ≤ 2^(cost w) :=
    Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le _ _)
  by_cases hbound : 2^(cost w-1) ≤ 2*q
  · exact hbound
  have hq : 2*q < 2^(cost w) := by omega
  rw [Nat.mod_eq_of_lt hq] at hmarker
  omega

/-- Each depth contributes at least one unit of dyadic cost. -/
theorem word_length_le_cost (w : List Nat) : w.length ≤ cost w := by
  induction w with
  | nil => simp [cost]
  | cons t ts ih => simp only [List.length_cons, cost]; omega

/-- No infinite source shadow paths from both original same-q feeders can
share the entire inverse-depth sequence, including an aperiodic one. -/
theorem no_common_infinite_feeder_depths (q : Nat)
    (p0 : BB6.Precision.InfiniteShadowPath (16*q+8) (12*q+4))
    (p1 : BB6.Precision.InfiniteShadowPath (16*q+9) (10*q+4))
    (hm0 : p0.m 0 = 0) (hz0 : p0.z 0 = 12*q+4)
    (hm1 : p1.m 0 = 0) (hz1 : p1.z 0 = 10*q+4)
    (hsame : ∀ n, p0.depth n = p1.depth n) : False := by
  let N : Nat := 2*q+2
  let w : List Nat := List.ofFn (fun j : Fin N => p0.depth j)
  have hwlen : w.length = N := List.length_ofFn
  have hne : w ≠ [] := by
    intro hw
    have he : w.length = 0 := by rw [hw]; rfl
    omega
  have hdep0 : ∀ i (hi : i < w.length),
      p0.depth (0+i) = w.get ⟨i,hi⟩ := by
    intro i hi
    simp only [Nat.zero_add, List.get_eq_getElem]
    dsimp [w]
    simp only [List.getElem_ofFn]
  have hdep1 : ∀ i (hi : i < w.length),
      p1.depth (0+i) = w.get ⟨i,hi⟩ := by
    intro i hi
    rw [← hsame (0+i)]
    exact hdep0 i hi
  have hr0 : Run (16*q+8) w 0 (12*q+4)
      (p0.m (0+w.length)) (p0.z (0+w.length)) := by
    have h := p0.run_of_list_segment 0 w hdep0
    simpa [hm0, hz0] using h
  have hr1 : Run (16*q+9) w 0 (10*q+4)
      (p1.m (0+w.length)) (p1.z (0+w.length)) := by
    have h := p1.run_of_list_segment 0 w hdep1
    simpa [hm1, hz1] using h
  have hbound := same_q_feeder_cost_bound q w
    (p0.m (0+w.length)) (p0.z (0+w.length))
    (p1.m (0+w.length)) (p1.z (0+w.length)) hne hr0 hr1
  have hcost : N ≤ cost w := by
    have := word_length_le_cost w
    omega
  have hexp : 2*q+1 ≤ cost w - 1 := by dsimp [N] at hcost; omega
  have hpow : 2^(2*q+1) ≤ 2^(cost w-1) :=
    Nat.pow_le_pow_right (by decide : 0<2) hexp
  have hstrict : 2*q < 2^(2*q+1) := by
    have hh := Nat.lt_two_pow_self (n := 2*q+1)
    omega
  omega

#print axioms same_q_feeder_marker
#print axioms same_q_feeder_cost_bound
#print axioms word_length_le_cost
#print axioms no_common_infinite_feeder_depths

end BB6.Agent9CrossFeeder
