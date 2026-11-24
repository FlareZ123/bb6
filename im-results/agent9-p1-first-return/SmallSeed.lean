import RenewalUnbounded

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 1000000

/-- Static-grid residue plus nonnegative clock correction. The correction
cannot consume the nearest upper grid margin when the seed is small. -/
theorem small_margin (M H d s j R U E : Nat)
    (hH : 0<H) (hHdiv : H ∣ M) (hRdiv : H ∣ R)
    (hd : 2≤d) (hs : j+2≤s) (hsmall : 4*(s+8)*d<M)
    (hR : R<M) (he : H*d=R+M*U) (hE : E≤s*U)
    (hEpos : 0<U → s-j≤E) (hHone : H=1 → U=0) :
    2≤R+E ∧ R+E+8+s≤M+j := by
  have hM : 0<M := by omega
  obtain ⟨r,hr⟩ := hRdiv
  obtain ⟨z,hz⟩ := hHdiv
  have hrz : r<z := by
    apply Nat.lt_of_mul_lt_mul_left (a:=H)
    omega
  have hRH : R+H≤M := by
    have hm := Nat.mul_le_mul_left H (show r+1≤z by omega)
    rw [Nat.mul_add,Nat.mul_one] at hm
    omega
  have h4E : 4*E≤H := by
    have hm := Nat.mul_le_mul_right U (Nat.le_of_lt hsmall)
    have hmul : 4*(s+8)*d*U=(4*(s+8)*U)*d := by ac_rfl
    rw [hmul] at hm
    have hle : (4*(s+8)*U)*d≤H*d := by omega
    have hh := Nat.le_of_mul_le_mul_right hle (by omega : 0<d)
    have hEU := Nat.mul_le_mul_left 4 hE
    have hsu := Nat.mul_le_mul_right U (show s≤s+8 by omega)
    have hsu' := Nat.mul_le_mul_left 4 hsu
    rw [←Nat.mul_assoc,←Nat.mul_assoc] at hsu'
    rw [←Nat.mul_assoc] at hEU
    omega
  constructor
  · by_cases hr0 : R=0
    · have hU : 0<U := by
        by_cases h0 : U=0
        · simp [hr0,h0] at he
          have hp := Nat.mul_pos hH (show 0<d by omega)
          omega
        · omega
      have h := hEpos hU
      omega
    · by_cases h1 : H=1
      · have hu := hHone h1
        simp [h1,hu] at he
        omega
      · have hrp : 0<r := by
          by_cases hh : r=0
          · simp [hh] at hr; omega
          · omega
        have hh := Nat.mul_le_mul_left H (show 1≤r by omega)
        simp at hh
        omega
  · by_cases hbig : 2*(s+8)<H
    · omega
    · have hm := Nat.mul_le_mul_right d (show H≤2*(s+8) by omega)
      have hh : 2*(2*(s+8)*d)=4*(s+8)*d := by grind only
      rw [←hh] at hsmall
      have hlt : 2*(H*d)<M := by omega
      have hu : U=0 := by
        by_cases h : U=0
        · exact h
        · have hh := Nat.mul_le_mul_left M (show 1≤U by omega)
          simp at hh
          omega
      have hE0 : E=0 := by simp [hu] at hE; omega
      have hR0 : R=H*d := by simp [hu] at he; omega
      have hsM : 2*(s+8)≤M := by
        have hm' := Nat.mul_le_mul_left (4*(s+8)) (show 1≤d by omega)
        simp at hm'
        omega
      omega

/-- The full moving-modulus orbit agrees with the static quotient word for
its first n unit steps (or any earlier prefix), under a polynomial-size
seed and clock deficit. No nonzero ideal phase hypothesis is required. -/
theorem small_grid_prefix (n q d s j : Nat)
    (hclock : q+s=7*2^n) (hd : 2≤d) (hj : j≤n) (hs : j+2≤s)
    (hsmall : 4*(s+8)*d<7*2^n) :
    ∃ R U E : Nat,
      R<7*2^n ∧ 2^j*d=R+7*2^n*U ∧ E≤s*U ∧
      (0<U → s-j≤E) ∧ run q d j=R+E ∧
      2≤run q d j ∧ run q d j+8≤q+j := by
  let M := 7*2^n
  have hM : 0<M := by dsimp [M]; have := Nat.two_pow_pos n; omega
  have hdM : d<M := by
    have hm := Nat.mul_le_mul_right d (show 1≤4*(s+8) by omega)
    simp at hm
    omega
  have hHdiv : ∀ i≤n, 2^i ∣ M := by
    intro i hi
    obtain ⟨a,ha⟩ := Nat.pow_dvd_pow 2 hi
    exact ⟨7*a,by dsimp [M]; rw [ha]; ac_rfl⟩
  have hRdiv : ∀ i≤n, ∀ R U : Nat, 2^i*d=R+M*U → 2^i∣R := by
    intro i hi R U he
    have hMU : 2^i∣M*U := Nat.dvd_mul_right_of_dvd (hHdiv i hi) U
    apply (Nat.dvd_add_iff_left hMU).mpr
    rw [←he]
    exact ⟨d,rfl⟩
  change ∃ R U E : Nat, R<M ∧ 2^j*d=R+M*U ∧ E≤s*U ∧ (0<U → s-j≤E) ∧ run q d j=R+E ∧ 2≤run q d j ∧ run q d j+8≤q+j
  induction j with
  | zero =>
    have hm := small_margin M 1 d s 0 d 0 0 (by decide) (by simp) (by simp) hd hs hsmall hdM (by simp) (by simp) (by omega) (by omega)
    exact ⟨d,0,0,hdM,by simp,by simp,by omega,by simp [run],by simpa [run] using hm.1,by simp [run]; omega⟩
  | succ j ih =>
    obtain ⟨R,U,E,hR,he,hE,hEpos,hrun,hlo,hhi⟩ := ih (by omega) (by omega)
    let x := bit (M-1) R
    let R' := unit (M-1) R
    let U' := 2*U+x
    let E' := 2*E+(s-(j+1))*x
    have hMs : M-1+1=M := by omega
    have hx : x=0 ∨ x=1 := by unfold x bit; split <;> simp
    have hstatic : 2*R=R'+M*x := by
      by_cases h : R<M-1
      · have hh := unit_equation (M-1) R h
        rw [hMs] at hh
        exact hh
      · have hR' : R=M-1 := by omega
        have hM2 : 2≤M := by omega
        have heq : R'=M-2 := by
          unfold R' unit
          rw [hMs,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
          omega
        have hx' : x=1 := by unfold x bit; rw [hMs]; simp [show M≤2*R by omega]
        rw [heq,hx']; omega
    have hR' : R'<M := by unfold R' unit; rw [hMs]; exact Nat.mod_lt _ hM
    have he' : 2^(j+1)*d=R'+M*U' := by
      rw [Nat.pow_succ]
      have hh : 2^j*2*d=2*(2^j*d) := by ac_rfl
      rw [hh,he]
      unfold U'
      simp only [Nat.mul_add,show M*(2*U)=2*(M*U) by ac_rfl]
      omega
    have hE' : E'≤s*U' := by
      rcases hx with hx|hx <;> simp only [U',E',hx,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.mul_add,show s*(2*U)=2*(s*U) by ac_rfl] <;> omega
    have hEpos' : 0<U' → s-(j+1)≤E' := by
      intro hU
      rcases hx with hx|hx
      · have hu : 0<U := by unfold U' at hU; omega
        have hh := hEpos hu
        unfold E'; rw [hx,Nat.mul_zero,Nat.add_zero]; omega
      · unfold E'; rw [hx,Nat.mul_one]; omega
    have hpow : 2≤2^(j+1) := Nat.pow_le_pow_right (show 0<2 by decide) (show 1≤j+1 by omega)
    have hm := small_margin M (2^(j+1)) d s (j+1) R' U' E' (by omega) (hHdiv _ hj) (hRdiv _ hj _ _ he') hd hs hsmall hR' he' hE' hEpos' (by omega)
    have hstep : 2*(R+E)=R'+E'+(q+j+1)*x := by
      rcases hx with hx|hx
      · simp [hx] at hstatic
        unfold E'; rw [hx,Nat.mul_zero,Nat.mul_zero,Nat.add_zero,Nat.add_zero]; omega
      · simp [hx] at hstatic
        unfold E'; rw [hx,Nat.mul_one,Nat.mul_one]; omega
    have hrun' : run q d (j+1)=R'+E' := by
      rw [run,unit,hrun,hstep,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
    exact ⟨R',U',E',hR',he',hE',hEpos',hrun',by rw [hrun']; exact hm.1,by rw [hrun']; omega⟩

/-- At one dyadic block boundary the residual is exactly the seed's
mod-seven phase, plus a small nonnegative correction. -/
theorem small_grid_end (n q d s : Nat) (hclock : q+s=7*2^n)
    (hd : 2≤d) (hs : n+2≤s) (hsmall : 4*(s+8)*d<7*2^n) :
    ∃ E : Nat, E≤s*d ∧ run q d n=2^n*(d%7)+E ∧ 2≤run q d n ∧ run q d n+8≤q+n := by
  obtain ⟨R,U,E,hR,he,hE,hEpos,hrun,hlo,hhi⟩ := small_grid_prefix n q d s n hclock hd (by omega) hs hsmall
  have hP := Nat.two_pow_pos n
  have hdiv : 2^n∣R := by
    have hm : 2^n∣7*2^n*U := by exact ⟨7*U,by ac_rfl⟩
    apply (Nat.dvd_add_iff_left hm).mpr
    rw [←he]
    exact ⟨d,rfl⟩
  obtain ⟨r,hr⟩ := hdiv
  have hr7 : r<7 := by apply Nat.lt_of_mul_lt_mul_left (a:=2^n); rw [←hr]; simpa [Nat.mul_comm] using hR
  have hmul : 7*2^n*U=2^n*(7*U) := by ac_rfl
  rw [hr,hmul,←Nat.mul_add] at he
  have hdEq := Nat.mul_left_cancel hP he
  have hmod : d%7=r := by rw [hdEq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr7]
  have hu : U≤d := by omega
  exact ⟨E,Nat.le_trans hE (Nat.mul_le_mul_left s hu),by rw [hrun,hr,hmod],hlo,hhi⟩

#print axioms small_margin
#print axioms small_grid_prefix
#print axioms small_grid_end
end BB6.Agent9Renewal
