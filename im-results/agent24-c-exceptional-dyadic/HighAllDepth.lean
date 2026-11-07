import AlternateDyadic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- An all-depth high stopping exclusion. Every admissible r (a multiple
    of eight, at least eight) is a forced inverse depth into the
    exceptional source-inaccessible dyadic cone. -/
theorem high_all_depth_eight_no_blank (r j m k : Nat)
    (hr : 8≤r) (hr0 : r%8=0)
    (hwidth : r+4≤2*m+2) (hj : j%16=0)
    (hparam : (j+3*m+3)%2^(r+4)=9*2^r)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let Q := 2^r
  let M := 2^(r+4)
  have hM : M=Q*16 := by
    dsimp [M,Q]
    rw [Nat.pow_add]
  have hQpos : 0<Q := Nat.pow_pos (by decide)
  have hMdivPow : M ∣ 2^(2*m+2) := by
    dsimp [M]
    exact Nat.pow_dvd_pow 2 hwidth
  obtain ⟨u,hu⟩ := hMdivPow
  have hMdivScore : M ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨u*(j+3),?_⟩
    rw [hu]
    ac_rfl
  have hstopmod : (k+j+3*m+5)%M=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hMdivScore
  have hPmod : (j+3*m+3)%M=9*Q := by
    simpa only [M,Q] using hparam
  have hMpos : 0<M := by rw [hM]; omega
  have hSumZero : ((k+2)%M+9*Q)%M=0 := by
    have hadd : (k+2+(j+3*m+3))%M=0 := by
      have heq : k+2+(j+3*m+3)=k+j+3*m+5 := by omega
      rw [heq]
      exact hstopmod
    rw [Nat.add_mod,hPmod] at hadd
    exact hadd
  have hKmod : (k+2)%M=7*Q := by
    have hRlt : (k+2)%M < M := Nat.mod_lt _ hMpos
    have hSumPos : 0 < (k+2)%M+9*Q := by omega
    have hSumBound : (k+2)%M+9*Q < 2*M := by
      rw [hM] at hRlt ⊢
      omega
    have hDivLess : ((k+2)%M+9*Q)/M < 2 :=
      (Nat.div_lt_iff_lt_mul hMpos).mpr hSumBound
    have hSplit := Nat.mod_add_div ((k+2)%M+9*Q) M
    rw [hSumZero] at hSplit
    have hDivNonzero : ((k+2)%M+9*Q)/M ≠0 := by
      intro he
      rw [he] at hSplit
      simp at hSplit
      omega
    have hDivPos : 0 < ((k+2)%M+9*Q)/M := Nat.pos_of_ne_zero hDivNonzero
    have hDivOne : ((k+2)%M+9*Q)/M=1 := by omega
    rw [hDivOne] at hSplit
    rw [hM] at hSplit ⊢
    omega
  let t := (k+2)/Q
  have hQdivM : Q ∣ M := by
    refine ⟨16,?_⟩
    rw [hM]
  have hmodQ : (k+2)%Q=0 := by
    have hNested := Nat.mod_mod_of_dvd (k+2) hQdivM
    rw [hKmod] at hNested
    have h7Q : (7*Q)%Q=0 := Nat.mod_eq_zero_of_dvd ⟨7,by ac_rfl⟩
    rw [h7Q] at hNested
    exact hNested.symm
  have hQfactor : k+2=Q*t := by
    dsimp [t]
    have hmodDiv := Nat.mod_add_div (k+2) Q
    rw [hmodQ] at hmodDiv
    simpa using hmodDiv.symm
  have ht16 : t%16=7 := by
    have hmodMul : Q*(t%16)=Q*7 := by
      have h := hKmod
      rw [hQfactor,hM] at h
      rw [Nat.mul_mod_mul_left] at h
      simpa only [Nat.mul_comm] using h
    exact Nat.mul_left_cancel hQpos hmodMul
  have ht8 : t%8=7 := by omega
  have hx : (2*j+3)%16=3 := by omega
  have hpair : (2*j+3+30*t)%32=21 := by omega
  exact alternate_dyadic_no_blank r (2*j+3) k t
    hr hr0 hx ht8 hpair hQfactor

#print axioms high_all_depth_eight_no_blank
end BB6.Agent46
