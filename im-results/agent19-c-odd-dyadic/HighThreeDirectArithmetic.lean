import Lean.Elab.Tactic.Omega

namespace BB6.Agent11HighThreeDirect

theorem pow_bound (m:Nat) (hm:1≤m) : 8*m+8≤2^(2*m+2) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => decide
    | succ n =>
      have hi : 8*(n+1)+8≤2^(2*(n+1)+2) := ih (by omega)
      have he : 2*(n+1+1)+2=(2*(n+1)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Exact high stopping equation and pairwise modular conditions
    place the target directly into the complementary full-depth
    dyadic odd-part-three inverse cone. -/
theorem high_three_direct_arithmetic (r j m k : Nat)
    (_hr : 2≤r) (hm : 3≤m) (hdepth : r+2≤2*m+2)
    (hm4 : m%4=(2*r+1)%4)
    (hpair : (j+3*m+3)%2^(r+2)=2^r)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u : Nat, 7≤u ∧ u%4=3 ∧ k+2=2^r*u ∧
      (2*j+3+2*k+4*r)%8=3 := by
  let R := (2:Nat)^r
  let P := (2:Nat)^(2*m+2)
  let Q := 2^(r+2)
  let D := j+3*m+3
  let S := k+2
  have hRpos : 0<R := by dsimp [R]; exact Nat.pow_pos (by decide)
  have hPpos : 0<P := by dsimp [P]; exact Nat.pow_pos (by decide)
  have hQ : Q=4*R := by
    dsimp [Q,R]
    rw [show r+2=r+2 by omega, Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  have hQpos : 0<Q := by omega
  have hdivP : Q∣P := by
    dsimp [Q,P]
    exact Nat.pow_dvd_pow 2 hdepth
  have hdivprod : Q∣P*(j+3) := by
    rcases hdivP with ⟨v,hv⟩
    refine ⟨v*(j+3),?_⟩
    rw [hv]
    simp only [Nat.mul_assoc]
  have hSplusD : S+D=P*(j+3) := by
    dsimp [S,D,P] at *
    omega
  have hSplus_mod : (S+D)%Q=0 := by
    rw [hSplusD]
    exact Nat.mod_eq_zero_of_dvd hdivprod
  have hDmod : D%Q=R := by
    simpa only [D,Q,R] using hpair
  have hSmod : S%Q=3*R := by
    have hSm : S%Q<Q := Nat.mod_lt _ hQpos
    rw [Nat.add_mod,hDmod] at hSplus_mod
    have hbounds : 0 < S%Q+R ∧ S%Q+R<2*Q := by omega
    have hdiv : Q∣S%Q+R := Nat.dvd_of_mod_eq_zero hSplus_mod
    obtain ⟨v,hv⟩ := hdiv
    have hvpos : 0<v := by
      by_cases hzero : v=0
      · simp [hzero] at hv
        omega
      · omega
    by_cases hveq : v=1
    · rw [hveq] at hv
      omega
    · have hv2 : 2≤v := by omega
      have hh : Q*2≤Q*v := Nat.mul_le_mul_left Q hv2
      omega
  let w := S/Q
  have hSrepr : S=R*(4*w+3) := by
    have h0 : S=3*R+Q*w := by
      calc
        S = S%Q+Q*(S/Q) := (Nat.mod_add_div S Q).symm
        _ = 3*R+Q*w := by rw [hSmod]
    calc
      S = 3*R+Q*w := h0
      _ = R*(4*w+3) := by
        rw [hQ]
        simp only [Nat.mul_add]
        ac_rfl
  have hbound : 8*m+8≤P := pow_bound m (by omega)
  have hjlow : j≤P*j := by
    have hP1 : 1≤P := by omega
    simpa using Nat.mul_le_mul_right j hP1
  have hP4R : 4*R≤P := by
    obtain ⟨v,hPv⟩ := hdivP
    have hvpos : 1≤v := by
      have hpositive : 0<Q*v := by rw [←hPv]; exact hPpos
      by_cases hv : v=0
      · simp [hv] at hpositive
      · omega
    have hq : Q≤Q*v := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hvpos
    have hqle : Q≤P := by rw [hPv]; exact hq
    omega
  have hSbig : 7*R≤S := by
    have hPmargin : 3*m+3≤P := by omega
    have hPu : 8*R≤2*P := by omega
    rw [Nat.mul_add] at hSplusD
    dsimp [D] at hSplusD
    omega
  have hw : 7≤4*w+3 := by
    have hbig : R*7≤R*(4*w+3) := by
      rw [←hSrepr]
      omega
    exact Nat.le_of_mul_le_mul_left hbig (by omega)
  have hmass : (2*j+3+2*k+4*r)%8=3 := by
    have hP4 : 4∣P := by
      dsimp [P]
      simpa only [show (2:Nat)^2=4 by decide] using
        (Nat.pow_dvd_pow 2 (by omega : 2≤2*m+2))
    have hPprod4 : 4∣P*(j+3) := by
      rcases hP4 with ⟨v,hPv⟩
      refine ⟨v*(j+3),?_⟩
      rw [hPv]
      simp only [Nat.mul_assoc]
    obtain ⟨v,hPv⟩ := hPprod4
    rw [Nat.mul_add] at hstop
    omega
  refine ⟨4*w+3,hw,?_ ,hSrepr,hmass⟩
  omega

#print axioms high_three_direct_arithmetic
end BB6.Agent11HighThreeDirect
