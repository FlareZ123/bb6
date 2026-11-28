import OrderReturn
set_option maxHeartbeats 0
namespace BB6.Agent9CyclicPrimitive
open BB6.Agent9ReturnGCD

/-- A primitive period p of an interior integer doubling carry modulo g
    can never divide the initial slope in the product g ∣ p*a(0).

    Proof: divisibility propagates backward from a(p)=a(0) through the
    exact doubling recurrence, without cancelling two modulo g. Thus
    every p*a(j) (j<p) is a multiple of g. Taking the integral quotient
    gives p distinct positive integers strictly below p, impossible.

    This removes the old coprimality and extra-period requirements from
    cyclic affine-clock determinant arguments. -/
theorem primitive_product_not_dvd
    (g : Int) (p : Nat) (a x : Nat → Int)
    (hg : 0<g) (hp : 0<p)
    (hinside : ∀ j≤p, 0<a j ∧ a j<g)
    (hstep : ∀ j<p, 2*a (j+1)=a j+g*x j)
    (hreturn : a p=a 0)
    (hdistinct : ∀ i j, i<j → j<p → a i≠a j) :
    ¬ g ∣ (p:Int)*a 0 := by
  intro hd
  have hlast : g ∣ (p:Int)*a p := by simpa only [hreturn] using hd
  have hback : ∀ k≤p, g ∣ (p:Int)*a (p-k) := by
    intro k hk
    induction k with
    | zero => simpa using hlast
    | succ k ih =>
      have hnext : (p-(k+1))+1=p-k := by omega
      have hpr := ih (by omega)
      rw [←hnext] at hpr
      obtain ⟨z,hz⟩ := hpr
      let j := p-(k+1)
      have hj : j<p := by dsimp [j]; omega
      have he := hstep j hj
      have heP : 2*((p:Int)*a (j+1)) =
          (p:Int)*a j+g*((p:Int)*x j) := by
        calc
          _ = (p:Int)*(2*a (j+1)) := by ac_rfl
          _ = (p:Int)*(a j+g*x j) := by rw [he]
          _ = (p:Int)*a j+g*((p:Int)*x j) := by
            rw [Int.mul_add]
            ac_rfl
      refine ⟨2*z-(p:Int)*x j,?_⟩
      change (p:Int)*a j=g*(2*z-(p:Int)*x j)
      have hz' : (p:Int)*a (j+1)=g*z := by simpa only [j] using hz
      rw [hz'] at heP
      have halg : g*(2*z-(p:Int)*x j)=
          2*(g*z)-g*((p:Int)*x j) := by
        simp only [Int.mul_sub,Int.mul_assoc]
        ac_rfl
      rw [halg]
      omega
  have hdivAll : ∀ j≤p, g ∣ (p:Int)*a j := by
    intro j hj
    have h := hback (p-j) (by omega)
    simpa only [show p-(p-j)=j by omega] using h
  classical
  let b : Nat → Int := fun j =>
    if hj : j≤p then Classical.choose (hdivAll j hj) else 0
  have hb : ∀ j≤p, (p:Int)*a j=g*b j := by
    intro j hj
    dsimp [b]
    simp only [dif_pos hj]
    exact Classical.choose_spec (hdivAll j hj)
  have hbi : ∀ j<p, 0<b j ∧ b j<(p:Int) := by
    intro j hj
    have hq := hb j (by omega)
    have ha := hinside j (by omega)
    have hppos : 0<(p:Int) := by omega
    have hl := Int.mul_pos hppos ha.1
    have hr := Int.mul_lt_mul_of_pos_left ha.2 hppos
    rw [Int.mul_comm (p:Int) g] at hr
    constructor
    · by_cases hz : 0<b j
      · exact hz
      · have hn := Int.mul_nonpos_of_nonneg_of_nonpos
          (show 0≤g by omega) (show b j≤0 by omega)
        omega
    · by_cases hr' : b j<(p:Int)
      · exact hr'
      · have hn := Int.mul_le_mul_of_nonneg_left
          (show (p:Int)≤b j by omega) (show 0≤g by omega)
        omega
  obtain ⟨i,j,hij,hjp,heq⟩ := interior_collision b p hp hbi
  have hi := hb i (by omega)
  have hj := hb j (by omega)
  rw [heq] at hi
  have he : (p:Int)*a i=(p:Int)*a j := by omega
  exact hdistinct i j hij hjp
    (Int.eq_of_mul_eq_mul_left (show (p:Int)≠0 by omega) he)

#print axioms primitive_product_not_dvd
end BB6.Agent9CyclicPrimitive
