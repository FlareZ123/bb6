import SheepAffine
import CoprimeAffine

namespace SheepFinite
open SheepAffine SheepWord

private theorem affine_gap_step (L N : Nat) (B : Int)
    (u v w : Nat) (huv : u ≤ v) (hvw : v ≤ w)
    (h1 : (L:Int)*v=(N:Int)*u+B)
    (h2 : (L:Int)*w=(N:Int)*v+B) :
    L*(w-v)=N*(v-u) := by
  have hdiff : (L:Int)*((w:Int)-v)=(N:Int)*((v:Int)-u) := by
    calc
      _ = (L:Int)*w-(L:Int)*v := by simp [Int.mul_sub]
      _ = ((N:Int)*v+B)-((N:Int)*u+B) := by rw [h2,h1]
      _ = (N:Int)*((v:Int)-u) := by simp [Int.mul_sub]; omega
  have hsub1 : ((w-v:Nat):Int)=(w:Int)-v := by omega
  have hsub2 : ((v-u:Nat):Int)=(v:Int)-u := by omega
  rw [←hsub1,←hsub2] at hdiff
  exact Int.ofNat.inj (by simpa only [Int.natCast_mul] using hdiff)

/-- For n+1 consecutive copies of a nonempty generic Sheep branch word,
the positive first word-boundary increment is at least 2^(n * C(w)).
This is a finite-horizon, arbitrary-start theorem. -/
theorem word_repetition_gap_bound
    (w : List (Nat × Nat)) (hw : w ≠ []) (n : Nat)
    (x : Nat → Nat)
    (hpath : ∀ i ≤ n, WordPath w (x i) (x (i+1)))
    (hinc : ∀ i ≤ n, x i < x (i+1)) :
    2^(n*wordCost w) ≤ x 1 - x 0 := by
  let p := wordParams w
  let d : Nat → Nat := fun i => x (i+1)-x i
  have hrec : ∀ i < n, p.L*d (i+1)=p.N*d i := by
    intro i hi
    have hi1 : i+1≤n := by omega
    have hp0 := holds_to_int_affine p (x i) (x(i+1))
      (word_path_holds w _ _ (hpath i (by omega)))
    have hp1 := holds_to_int_affine p (x(i+1)) (x(i+2))
      (word_path_holds w _ _ (by simpa [show i+1+1=i+2 by omega] using hpath (i+1) hi1))
    have hdelta := affine_gap_step p.L p.N ((p.P:Int)-(p.Q:Int))
       (x i) (x(i+1)) (x(i+2))
       (Nat.le_of_lt (hinc i (by omega)))
       (Nat.le_of_lt (by simpa [show i+1+1=i+2 by omega] using hinc (i+1) hi1))
       hp0 hp1
    simpa [d, show i+1+1=i+2 by omega] using hdelta
  have hpos : 0 < d 0 := Nat.sub_pos_of_lt (hinc 0 (by omega))
  have hb := finite_chain_gap_lower_bound p.L p.N n (word_coprime w) d hpos hrec
  rw [word_scale] at hb
  simpa only [←pow_mul, d] using hb

#print axioms word_repetition_gap_bound
end SheepFinite
