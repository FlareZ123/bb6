import CyclicPrimitive
set_option maxHeartbeats 0
namespace BB6.Agent9AntiShortCore
open BB6.Agent9ReturnGCD

/-- Backward divisibility transport with an arbitrary coefficient k.
    In contrast with forward propagation, no invertibility of 2 modulo g
    is needed: k*a_j = 2*(k*a_(j+1)) - g*(k*x_j). -/
theorem backward_divisible (g k : Int) (p : Nat)
    (a x : Nat → Int)
    (hs : ∀ j<p, 2*a (j+1)=a j+g*x j)
    (hd : g∣k*a p) :
    ∀ j≤p, g∣k*a j := by
  have hback : ∀ t≤p, g∣k*a (p-t) := by
    intro t ht
    induction t with
    | zero => simpa using hd
    | succ t ih =>
      have hn : (p-(t+1))+1=p-t := by omega
      have h := ih (by omega)
      rw [←hn] at h
      obtain ⟨z,hz⟩ := h
      let j := p-(t+1)
      have hj : j<p := by dsimp [j]; omega
      have he := hs j hj
      have heK : 2*(k*a (j+1)) = k*a j+g*(k*x j) := by
        calc
          _ = k*(2*a (j+1)) := by ac_rfl
          _ = k*(a j+g*x j) := by rw [he]
          _ = k*a j+g*(k*x j) := by
            rw [Int.mul_add]
            ac_rfl
      refine ⟨2*z-k*x j,?_⟩
      change k*a j=g*(2*z-k*x j)
      have hz' : k*a (j+1)=g*z := by simpa only [j] using hz
      rw [hz'] at heK
      have halg : g*(2*z-k*x j)=2*(g*z)-g*(k*x j) := by
        simp only [Int.mul_sub,Int.mul_assoc]
        ac_rfl
      rw [halg]
      omega
  intro j hj
  have h := hback (p-j) (by omega)
  simpa only [show p-(p-j)=j by omega] using h

/-- In the interior, the doubling-carry dynamics has unique predecessors,
    so any collision a_i=a_(i+p) propagates to a genuine return a_0=a_p. -/
theorem collision_returns_to_zero (g : Int) (a x : Nat → Int)
    (L p : Nat)
    (hb : ∀ j≤L, 0<a j ∧ a j<g)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ i, i+p≤L → a i=a (i+p) → a 0=a p := by
  intro i
  induction i with
  | zero =>
    intro _ h
    simpa using h
  | succ i ih =>
    intro hi he
    have h1 := hs i (by omega)
    have h2 := hs (i+p) (by omega)
    rw [show i+p+1=i+1+p by omega,←he] at h2
    have h := interior_prev_unique g (a i) (a (i+p))
      (a (i+1)) (x i) (x (i+p))
      (hb i (by omega)) (hb (i+p) (by omega))
      (hx i (by omega)) (hx (i+p) (by omega)) h1 h2
    exact ih (by omega) h

/-- If K distinct positive integer slots are impossible, an interior
    slope whose K-scaled orbit is divisible by g must return before K.
    The statement is independent of any numerical size of g. -/
theorem divisible_cycle_has_short_return (g : Int) (K L : Nat)
    (a x : Nat → Int)
    (hg : 0<g) (hK : 0<K) (hKL : K≤L)
    (hb : ∀ j≤L, 0<a j ∧ a j<g)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hd : ∀ j≤K, g∣(K:Int)*a j) :
    ∃ p, 0<p ∧ p<K ∧ a p=a 0 := by
  classical
  let b : Nat → Int := fun j =>
    if hj : j≤K then Classical.choose (hd j hj) else 0
  have hquot : ∀ j≤K, (K:Int)*a j=g*b j := by
    intro j hj
    dsimp [b]
    simp only [dif_pos hj]
    exact Classical.choose_spec (hd j hj)
  have hbin : ∀ j<K, 0<b j ∧ b j<(K:Int) := by
    intro j hj
    have hq := hquot j (by omega)
    have ha := hb j (by omega)
    have hpos : 0<(K:Int) := by omega
    have hl := Int.mul_pos hpos ha.1
    have hr := Int.mul_lt_mul_of_pos_left ha.2 hpos
    rw [Int.mul_comm (K:Int) g] at hr
    constructor
    · by_cases h : 0<b j
      · exact h
      · have hn := Int.mul_nonpos_of_nonneg_of_nonpos
          (show 0≤g by omega) (show b j≤0 by omega)
        omega
    · by_cases h : b j<(K:Int)
      · exact h
      · have hn := Int.mul_le_mul_of_nonneg_left
          (show (K:Int)≤b j by omega) (show 0≤g by omega)
        omega
  obtain ⟨i,j,hij,hjK,he⟩ := interior_collision b K hK hbin
  have hi := hquot i (by omega)
  have hj := hquot j (by omega)
  rw [he] at hi
  have hEq : (K:Int)*a i=(K:Int)*a j := by omega
  have haEq : a i=a j :=
    Int.eq_of_mul_eq_mul_left (show (K:Int)≠0 by omega) hEq
  let p := j-i
  have hip : i+p=j := by dsimp [p]; omega
  have heReturn := collision_returns_to_zero g a x L p hb hx hs i
    (by omega) (by rwa [hip])
  exact ⟨p,by dsimp [p]; omega,by dsimp [p]; omega,heReturn.symm⟩

#print axioms backward_divisible
#print axioms collision_returns_to_zero
#print axioms divisible_cycle_has_short_return
end BB6.Agent9AntiShortCore
