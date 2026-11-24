import P1CarryBlankArithmetic
namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExtinction

/-- A complementary word identity for the left coordinate, at every cost. -/
theorem micro_left_word (n m v w : Nat) (h : Micro n m v w) (hm : 0<m) (hn : 14≤n) :
    ∃ xs : List Bool, xs.length+1=m ∧
      2^m*w+(n+2+absSum n 1 xs)=total n*(1+bitMass 1 xs) := by
  induction h with
  | root => omega
  | one m v w v' w' h hv hw ih =>
    by_cases hm0 : m=0
    · subst m
      clear ih
      cases h with
      | root =>
        refine ⟨[],by simp,?_⟩
        simp [absSum,bitMass]
        have htotal := total_large n hn
        omega
    · obtain ⟨xs,hx,he⟩ := ih (by omega)
      refine ⟨xs++[false],by simp; omega,?_⟩
      have hf := expr_snoc n xs false
      simp [expr] at hf
      have hF : absSum n 1 (xs++[false])=absSum n 1 xs := by omega
      rw [hF,bitMass_snoc]
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero,Nat.pow_succ,Nat.mul_assoc,← hw]
      exact he
  | zero m v w v' w' h hm0 hv hw ih =>
    obtain ⟨xs,hx,he⟩ := ih hm0
    refine ⟨xs++[true],by simp; omega,?_⟩
    have hidx : 1+xs.length=m := by omega
    have hf := expr_snoc n xs true
    simp only [expr,ite_true,hidx] at hf
    have hF : absSum n 1 (xs++[true])=absSum n 1 xs+weight n m := by omega
    have hw' : 2^m*w+2^m*total n=2^m*(2*w')+2^m*(n+m+3) := by
      rw [← Nat.mul_add,← Nat.mul_add,hw]
    have hweight : weight n m=2^m*(n+m+3) := by unfold weight; rw [Nat.mul_comm]; congr 1; omega
    calc
      2^(m+1)*w'+(n+2+absSum n 1 (xs++[true])) =
          (2^m*(2*w')+2^m*(n+m+3))+(n+2+absSum n 1 xs) := by
        rw [hF,hweight,Nat.pow_succ]; ac_rfl
      _ = (2^m*w+2^m*total n)+(n+2+absSum n 1 xs) := by rw [← hw']
      _ = (2^m*w+(n+2+absSum n 1 xs))+total n*2^m := by ac_rfl
      _ = total n*(1+bitMass 1 xs)+total n*2^m := by rw [he]
      _ = total n*(1+bitMass 1 (xs++[true])) := by
        rw [bitMass_snoc,hidx]; simp only [ite_true,Nat.mul_add]; ac_rfl

theorem absSum_upper (n j A : Nat) (xs : List Bool) (hA : n+2+j+xs.length≤A) :
    absSum n j xs≤A*bitMass j xs := by
  induction xs generalizing j with
  | nil => simp [absSum,bitMass]
  | cons b bs ih =>
    have h := ih (j+1) (by simp at hA; omega)
    have hcoef : n+3+j≤A := by simp at hA; omega
    have hweight := Nat.mul_le_mul_right (2^j) hcoef
    cases b <;> simp [absSum,bitMass,weight,Nat.mul_add] <;> omega

/-- Uniform left margin, including the last level m=n. -/
theorem micro_left_margin (n m v w : Nat) (hn : 14≤n) (hm : 0<m) (hmn : m≤n)
    (h : Micro n m v w) : total n≤(n+m+2)*(w+1) := by
  obtain ⟨xs,hx,he⟩ := micro_left_word n m v w h hm hn
  let A := n+m+2
  let D := 2^m
  let R := 1+bitMass 1 xs
  let L := n+2+absSum n 1 xs
  change D*w+L=total n*R at he
  have hLpos : 0<L := by dsimp [L]; omega
  have hL : L≤A*R := by
    have hh := absSum_upper n 1 A xs (by dsimp [A]; omega)
    dsimp [L,R]; rw [Nat.mul_add]; simp only [Nat.mul_one]; dsimp [A] at *; omega
  have hd : D ∣ total n := by
    unfold D total
    exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hmn) 7
  have hdL : D ∣ L := by
    have h1 : D ∣ D*w := Nat.dvd_mul_right _ _
    have h2 : D ∣ D*w+L := he ▸ Nat.dvd_mul_right_of_dvd hd R
    exact (Nat.dvd_add_right h1).mp h2
  have hDL : D≤L := Nat.le_of_dvd hLpos hdL
  have hDA : D≤A*R := by omega
  have hT : A≤total n := by
    have hp := pow2_ge_1100_mul n hn
    dsimp [A,total]; omega
  have h1 : (total n-A)*R≤D*w := by
    have hh := Nat.sub_mul (total n) A R
    omega
  have h2 := Nat.mul_le_mul_left (total n-A) hDA
  have h3 := Nat.mul_le_mul_left A h1
  have h4 : (total n-A)*D≤A*(D*w) := by
    calc
      (total n-A)*D ≤ (total n-A)*(A*R) := h2
      _ = A*((total n-A)*R) := by ac_rfl
      _ ≤ A*(D*w) := h3
  have hpD : 0<D := Nat.two_pow_pos _
  have h5 : D*(total n-A)≤D*(A*w) := by
    simpa only [Nat.mul_comm D, Nat.mul_left_comm, Nat.mul_assoc] using h4
  have h6 := Nat.le_of_mul_le_mul_left h5 hpD
  change total n≤A*(w+1)
  rw [Nat.mul_add,Nat.mul_one]
  omega

theorem pow2_ge_square (n : Nat) (hn : 14≤n) : 16*(n+1)*(n+1)≤2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : n=13
    · subst n; decide
    · have hp := ih (by omega)
      have hmul := Nat.mul_le_mul_right n (show 2≤n by omega)
      have hs : (n+2)*(n+2)≤2*((n+1)*(n+1)) := by
        simp only [Nat.add_mul,Nat.mul_add] 
        omega
      have hh := Nat.mul_le_mul_left 16 hs
      have h1 : 16*(n+1+1)*(n+1+1)≤2*(16*(n+1)*(n+1)) := by
        simpa only [show n+1+1=n+2 by omega, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
      rw [Nat.pow_succ]
      omega

/-- No loss in the left margin even when extinction is at layer n. -/
theorem critical_large_left_full (n K b d m : Nat) (hK : 0<K) (hn : 14≤n)
    (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m) : n+3*K+10≤b/4 := by
  have hm := critical_cost_lt n K b d m hn hK hKn hz h
  have hp := pow2_ge_square n hn
  have hlin := pow2_ge_1100_mul n hn
  by_cases hm0 : m=0
  · subst m
    cases h with
    | root => unfold criticalLeft; omega
  · have hM := source_to_micro n b d m hn h
    have hmargin := micro_left_margin n m ((d-1)/2) ((b+12)/2) hn (by omega) (by omega) hM
    by_cases hb : n+3*K+10≤b/4
    · exact hb
    · have hw : (b+12)/2+1≤10*(n+1) := by omega
      have hA : n+m+2≤2*(n+1) := by omega
      have hprod := Nat.mul_le_mul hA hw
      have hrew : 2*(n+1)*(10*(n+1))=20*((n+1)*(n+1)) := by calc
        _ = (2*10)*((n+1)*(n+1)) := by ac_rfl
        _ = _ := by rfl
      rw [hrew] at hprod
      have hsq : 0<(n+1)*(n+1) := Nat.mul_pos (by omega) (by omega)
      have hp' : 16*((n+1)*(n+1))≤2^n := by simpa only [Nat.mul_assoc] using hp
      unfold total at hmargin
      omega

#print axioms micro_left_margin
#print axioms critical_large_left_full
end BB6.P1CarryExact
