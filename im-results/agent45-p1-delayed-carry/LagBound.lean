import LagCert
import LagMicro
import LagMargin
namespace BB6.Agent45.DelayedCarry
open BB6.Agent45.LagMargin (early_margin tail_margin)
open BB6.P1CarryExact (Micro)

theorem early_word_margin (n m v B A L : Nat) (hm : m≤n) (hA : A≤2^n)
    (h1 : 2^m*v<total n*B) (h2 : total n*B≤2^m*v+A*B)
    (hgap : A*L<6*2^n) : L<v := by
  let F := total n*B-2^m*v
  have hF : F≤A*B := by dsimp [F]; omega
  have hpos : 0<F := by dsimp [F]; omega
  have hmass : 2^m*v+F=7*2^n*B := by unfold F; simp only [total] at *; omega
  have hd : (2:Nat)^m∣total n := by
    unfold total
    exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hm) 7
  have hdF : (2:Nat)^m∣F := Nat.dvd_sub (Nat.dvd_mul_right_of_dvd hd B) (Nat.dvd_mul_right _ _)
  exact early_margin (2^n) (2^m) A L B F v (Nat.two_pow_pos _) hA hmass hF (Nat.le_of_dvd hpos hdF) hgap

theorem late_word_margin (n j v B A L : Nat) (hA : A≤2^n)
    (h1 : 2^(n+j)*v<total n*B) (h2 : total n*B≤2^(n+j)*v+A*B)
    (hgap : A*L*2^j<6*2^n*((7*B)%2^j)) : L<v := by
  let F := total n*B-2^(n+j)*v
  have hF : F≤A*B := by dsimp [F]; omega
  have hmass : 2^n*2^j*v+F=7*2^n*B := by
    rw [← Nat.pow_add]
    unfold F
    simp only [total] at *
    omega
  exact tail_margin (2^n) (2^j) A L B F v (Nat.two_pow_pos _) hA hmass hF (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hgap)

theorem complement_residue (m j B : Nat) (hj : j≤m) (hB : B≤2^m)
    (hr : 0<(7*B)%2^j) : (7*(2^m-B))%2^j=2^j-(7*B)%2^j := by
  let D := 2^j
  let a := 7*B%D
  let b := 7*(2^m-B)%D
  have hD : 0<D := Nat.two_pow_pos _
  have ha : a<D := Nat.mod_lt _ hD
  have hb : b<D := Nat.mod_lt _ hD
  have hsum : 7*B+7*(2^m-B)=7*2^m := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hB]
  have hd : D∣7*2^m := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hj) 7
  have hmod : (a+b)%D=0 := by
    dsimp [a,b]
    rw [← Nat.add_mod,hsum]
    exact Nat.dvd_iff_mod_eq_zero.mp hd
  have hle : D≤a+b := by
    by_cases h : a+b<D
    · rw [Nat.mod_eq_of_lt h] at hmod
      change 0<a at hr
      omega
    · omega
  have hlt : a+b-D<D := by omega
  have hm : (a+b)%D=(a+b-D)%D := Nat.mod_eq_sub_mod hle
  rw [hm,Nat.mod_eq_of_lt hlt] at hmod
  change b=D-a
  omega

theorem cert_micro_bounds (n K s : Nat) (hn : 14≤n) (heven : n%2=0)
    (hs : 1≤s) (hK : K=n+s) (hA : n+K+2≤2^n)
    (hgap : (n+K+2)*marginSize n K<6*2^n) (hcert : Cert n K s []) :
    ∀ m v w, Micro n m v w → m<K ∧ (0<m → marginSize n K<v) ∧ marginSize n K<w := by
  intro m v w hM
  by_cases hm : m=0
  · subst m
    cases hM with
    | root =>
      have hL := Nat.mul_le_mul_right (marginSize n K) (show 1≤n+K+2 by omega)
      simp only [Nat.one_mul] at hL
      unfold BB6.P1CarryExact.total
      exact ⟨by omega,by omega,by omega⟩
  · obtain ⟨B,a,htr,hq,hbd⟩ := micro_trace n m v w hn heven hM (by omega)
    have hcost : m<K := by
      by_cases h : m<K
      · exact h
      · exact False.elim (no_trace_of_empty n s hs hcert.cover m B a (by omega) htr)
    rcases hbd with ⟨hv1,hv2,hw1,hw2⟩
    have hB := (trace_bounds n m B a htr).2.1
    have hVR := Nat.mul_le_mul_right B (show n+m+2≤n+K+2 by omega)
    have hWR := Nat.mul_le_mul_right (2^m-B) (show n+m+2≤n+K+2 by omega)
    have hv2' : total n*B≤2^m*v+(n+K+2)*B := by omega
    have hw2' : total n*(2^m-B)≤2^m*w+(n+K+2)*(2^m-B) := by omega
    refine ⟨hcost,?_,?_⟩
    · intro _
      by_cases hmn : m≤n
      · exact early_word_margin n m v B _ _ hmn hA hv1 hv2' hgap
      · let j := m-n
        have hj : n+j=m := by dsimp [j]; omega
        have htr' : Trace n (n+j) B a := by rw [hj]; exact htr
        have hg := hcert.margins j (by dsimp [j]; omega) (by dsimp [j]; omega) B a htr'
        have hres := Nat.mul_le_mul_left (6*2^n) (Nat.min_le_left ((7*B)%2^j) (2^j-(7*B)%2^j))
        change (n+K+2)*marginSize n K*2^j<6*2^n*resMin j B at hg
        unfold resMin at hg
        apply late_word_margin n j v B _ _ hA (by rw [hj]; exact hv1) (by rw [hj]; exact hv2')
        omega
    · by_cases hmn : m≤n
      · exact early_word_margin n m w (2^m-B) _ _ hmn hA hw1 hw2' hgap
      · let j := m-n
        have hj : n+j=m := by dsimp [j]; omega
        have htr' : Trace n (n+j) B a := by rw [hj]; exact htr
        have hg := hcert.margins j (by dsimp [j]; omega) (by dsimp [j]; omega) B a htr'
        have hpos : 0<(7*B)%2^j := by
          by_cases h : (7*B)%2^j=0
          · simp [resMin,h] at hg
          · omega
        have hcomp := complement_residue m j B (by omega) (by omega) hpos
        have hres := Nat.mul_le_mul_left (6*2^n) (Nat.min_le_right ((7*B)%2^j) (2^j-(7*B)%2^j))
        unfold resMin at hg
        apply late_word_margin n j w (2^m-B) _ _ hA (by rw [hj]; exact hw1) (by rw [hj]; exact hw2')
        rw [hcomp]
        omega

#print axioms cert_micro_bounds
end BB6.Agent45.DelayedCarry
