import CSixthSixSeven
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenSixthPullback

open BB6.Agent46

private theorem power_linear_bound (m : Nat) :
    4*m+4 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [show 2*(m+1)+2=2*m+2+2 by omega, Nat.pow_add]
      change 4*(m+1)+4 ≤ (2:Nat)^(2*m+2)*4
      omega

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ (2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hP := power_linear_bound m
  have hm : 3*m+5 ≤ 3*(2:Nat)^(2*m+2) := by omega
  rw [Nat.mul_add]
  omega

private theorem high_stop_identity (j m : Nat) :
    (2:Nat)^(2*m+2)*(j+3) - (j+3*m+5) + j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
  exact Nat.sub_add_cancel (high_score_nonnegative j m)

private theorem pullback_forces_m_ge7 (j m u v : Nat)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v) :
    7≤m := by
  have hstop : (574+1024*v)+j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
    rw [←hk]
    simpa using high_stop_identity j m
  rw [hj] at hstop
  by_cases hge : 7≤m
  · exact hge
  · have hmle : m≤6 := by omega
    rcases (show m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 by omega)
      with h0|h1|h2|h3|h4|h5|h6
    all_goals subst m
    all_goals simp at hstop
    all_goals omega

private theorem mod_1024_cancel_64 (v w : Nat)
    (h : (574+1024*v)%65536=(574+1024*w)%65536) :
    v%64=w%64 := by
  omega

theorem image_pullback_iff_congruence_a12_sixth (j m : Nat) :
    (∃ u v, j=319+512*u ∧
      (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v ∧
      (29*u+v)%64=13) ↔
    j%512=319 ∧ (3*m+71*j+57097)%65536=0 := by
  constructor
  · rintro ⟨u,v,hj,hk,hsector⟩
    have hm7 := pullback_forces_m_ge7 j m u v hj hk
    have hstop : (574+1024*v)+j+3*m+5 =
        (2:Nat)^(2*m+2)*(j+3) := by
      rw [←hk]
      simpa using high_stop_identity j m
    have hpow : 65536 ∣ (2:Nat)^(2*m+2) := by
      have hp : (2:Nat)^16 ∣ (2:Nat)^(2*m+2) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^16=65536 by decide] using hp
    have hprod : 65536 ∣ (2:Nat)^(2*m+2)*(j+3) := by
      obtain ⟨q,hq⟩ := hpow
      refine ⟨q*(j+3),?_⟩
      rw [hq]
      ac_rfl
    have hmod : ((574+1024*v)+j+3*m+5)%65536=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hprod
    have hjmod : j%512=319 := by
      rw [hj]
      omega
    have hcong : (3*m+71*j+57097)%65536=0 := by
      rw [hj] at hmod ⊢
      omega
    exact ⟨hjmod,hcong⟩
  · rintro ⟨hjmod,hcong⟩
    let u : Nat := j/512
    have hj : j=319+512*u := by
      dsimp [u]
      have hd := Nat.mod_add_div j 512
      rw [hjmod] at hd
      omega
    have hm512 : m%512=42 := by
      have hdiv : 512 ∣ 65536 := by decide
      have hmod512 : (3*m+71*j+57097)%512=0 := by
        calc
          (3*m+71*j+57097)%512 =
              ((3*m+71*j+57097)%65536)%512 := by
            symm
            exact Nat.mod_mod_of_dvd _ hdiv
          _ = 0 := by rw [hcong]
      rw [hj] at hmod512
      omega
    have hm42 : 42≤m := by
      have hle := Nat.mod_le m 512
      omega
    let k : Nat := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
    have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
      dsimp [k]
      simpa using high_stop_identity j m
    have hpow : 65536 ∣ (2:Nat)^(2*m+2) := by
      have hp : (2:Nat)^16 ∣ (2:Nat)^(2*m+2) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^16=65536 by decide] using hp
    have hprod : 65536 ∣ (2:Nat)^(2*m+2)*(j+3) := by
      obtain ⟨q,hq⟩ := hpow
      refine ⟨q*(j+3),?_⟩
      rw [hq]
      ac_rfl
    have hmodStop : (k+j+3*m+5)%65536=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hprod
    have hcong' : (3*m+79746+36352*u)%65536=0 := by
      rw [hj] at hcong
      omega
    have hstop' : (k+324+512*u+3*m)%65536=0 := by
      rw [hj] at hmodStop
      omega
    have hmodK : k%65536=(13886+35840*u)%65536 := by
      omega
    have hdiv : 1024 ∣ 65536 := by decide
    have hkmod1024 : k%1024=574 := by
      calc
        k%1024 = (k%65536)%1024 :=
          (Nat.mod_mod_of_dvd k hdiv).symm
        _ = ((13886+35840*u)%65536)%1024 := by rw [hmodK]
        _ = (13886+35840*u)%1024 :=
          Nat.mod_mod_of_dvd (13886+35840*u) hdiv
        _ = 574 := by omega
    let v : Nat := k/1024
    have hdecomp := Nat.mod_add_div k 1024
    have hk : k=574+1024*v := by
      dsimp [v]
      omega
    have hright : 13886+35840*u=574+1024*(13+35*u) := by omega
    have hmodEq :
        (574+1024*v)%65536=(574+1024*(13+35*u))%65536 := by
      calc
        (574+1024*v)%65536 = k%65536 := by rw [hk]
        _ = (13886+35840*u)%65536 := hmodK
        _ = (574+1024*(13+35*u))%65536 := by rw [←hright]
    have hv64 : v%64=(13+35*u)%64 :=
      mod_1024_cancel_64 v (13+35*u) hmodEq
    have hsector : (29*u+v)%64=13 := by omega
    have hk' :
        (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v := by
      simpa [k] using hk
    exact ⟨u,v,hj,hk',hsector⟩

theorem blank_ne_parameter_congruence_a12_sixth (j m time : Nat)
    (hjmod : j%512=319)
    (hcong : (3*m+71*j+57097)%65536=0) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (2*j+3,(2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)) := by
  obtain ⟨u,v,hj,hk,hsector⟩ :=
    (image_pullback_iff_congruence_a12_sixth j m).2 ⟨hjmod,hcong⟩
  have hblank :=
    BB6.Agent12SevenSixth.blank_ne_band_a12_sixth u v time hsector
  have hx : 2*j+3=641+1024*u := by omega
  intro hrun
  apply hblank
  rw [hx,hk] at hrun
  exact hrun

#print axioms image_pullback_iff_congruence_a12_sixth
#print axioms blank_ne_parameter_congruence_a12_sixth

end BB6.Agent12SevenSixthPullback
