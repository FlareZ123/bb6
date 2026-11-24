import HighNegativeShadow
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13HighCylinder
open BB6.Agent13AffineCone BB6.Agent13NegativeShadow BB6.Agent13HighShadow BB6.Agent46
private theorem weaken (b c p : Nat) (hcb : c≤b) (h : 2^b∣p) : 2^c∣p :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 hcb) h

private theorem cancel_pow (b r p : Nat) (hr : r≤b) (h : 2^b∣2^r*p) : 2^(b-r)∣p := by
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide : 0<(2:Nat)))
  rw [Nat.mul_comm (2^r) (2^(b-r)),Nat.pow_sub_mul_pow 2 hr]
  exact h

private theorem complement_half (p q d : Nat) (hd : 0<d)
    (hq : q%(2*d)=d) (h : 2*d∣p+q) : p%(2*d)=d := by
  have hz := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod,hq] at hz
  have hp := Nat.mod_lt p (by omega : 0<2*d)
  obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hz
  have hk1 : k=1 := by
    by_cases hk0 : k=0
    · subst k; omega
    · by_cases hne : k=1
      · exact hne
      · have hge : 2≤k := by omega
        have hmul := Nat.mul_le_mul_left (2*d) hge
        omega
  subst k
  omega


private theorem pow_bound (m : Nat) : 4*m+4≤(2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    change 4*(m+1)+4≤2^(2*m+2)*4
    omega


def highCheckAt (f b j m : Nat) : Bool :=
  let v := hv j m
  decide (2≤j ∧ j≤3*m ∧ 1≤m ∧ v+1≤b ∧ hq j m % 2^(v+1)=2^v ∧ hq j m < 2^b) &&
  (if (j+3*m+5)%2=0 then runCertAt f (b-1) (hd j m) else true) &&
  (List.range (v+1)).all (fun n => if n+2≤v ∧ n%2=ho j m then
    goodHi j m n && runCertAt f (b-(n+2)) (hh j m n) else true)

private theorem mod2_of_dvd (b x : Nat) (hb : 1≤b) (hx : 2^b∣x) : x%2=0 :=
  Nat.mod_eq_zero_of_dvd (weaken b 1 x hb hx)

theorem high_cylinder_exclusion (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f b j0 m0 j m k : Nat) (h : highCheckAt f b j0 m0=true)
    (hjj : j0≤j) (hmm : m0≤m) (hb : b≤2*m+2)
    (hjcon : 2^b∣j-j0) (hmcon : 2^b∣m-m0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬reach (2*j+3) k := by
  simp only [highCheckAt,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hj0,hj0m0,hm0,hvb,hvmod,hqbound⟩,hdir⟩,hhigh⟩ := h
  let v := hv j0 m0
  let P := 2^(2*m+2)*(j+3)
  let J := j-j0
  let M := m-m0
  have hP : 2^b∣P := weaken _ _ P hb ⟨j+3,rfl⟩
  have hb1 : 1≤b := by omega
  have hP2 : P%2=0 := mod2_of_dvd _ _ hb1 hP
  have hJ2 : J%2=0 := mod2_of_dvd _ _ hb1 hjcon
  have hM2 : M%2=0 := mod2_of_dvd _ _ hb1 hmcon
  have hJ : j=j0+J := by dsimp [J]; omega
  have hM : m=m0+M := by dsimp [M]; omega
  have hPbound : 4*m+4≤2^(2*m+2) := pow_bound m
  have hP16 : 16≤(2:Nat)^(2*m+2) := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 4≤2*m+2)
  have hPb : j+3*(2^(2*m+2))≤P := by
    dsimp [P]
    rw [Nat.mul_add]
    have hh : 1*j≤2^(2*m+2)*j := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.one_mul] at hh
    rw [Nat.mul_comm 3]
    omega
  change k+j+3*m+5=P at hstop
  have hk8 : 8≤k := by omega
  have hsumpar : (2*j+3+k)%2=ho j0 m0 := by unfold ho hs; omega
  have hsum : 2*j+3+k+ho j0 m0+hq j0 m0+3*M=P+J := by unfold hq hs ho; omega
  have hdiv3M : 2^b∣3*M := Nat.dvd_trans hmcon (Nat.dvd_mul_left M 3)
  have hdivQ : 2^b∣2*j+3+k+ho j0 m0+hq j0 m0 := by
    have H : 2^b∣P+J := Nat.dvd_add hP hjcon
    rw [←hsum] at H
    have H' := Nat.dvd_sub H hdiv3M
    simpa using H'
  have hpow : 2^(v+1)=2*2^v := by rw [Nat.pow_succ,Nat.mul_comm]
  have hmod : (2*j+3+k+(2*j+3+k)%2)%2^(v+1)=2^v := by
    rw [hsumpar,hpow]
    change hq j0 m0 % 2^(v+1)=2^v at hvmod
    rw [hpow] at hvmod
    apply complement_half _ _ _ (Nat.pow_pos (by decide)) hvmod
    rw [←hpow]
    exact weaken _ _ _ hvb hdivQ
  have hgt : 2^v<2*j+3+k+(2*j+3+k)%2 := by
    have hle : 2^v≤2^(2*m+2) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hsumpar]
    omega
  intro hr
  obtain ⟨a,l,hrp,hp⟩ := parent _ _ (by omega) hk8 hr
  rcases parent_equations a l (2*j+3) k v hk8 hmod hgt hp with H|H
  · obtain ⟨hke,ha,hl⟩ := H
    have hpar : (j0+3*m0+5)%2=0 := by omega
    simp only [hpar,if_true] at hdir
    have ha' : a+(hd j0 m0).x+3*M=P+J := by unfold hd hs; simp; omega
    have hl' : 2*(l+(hd j0 m0).y)+J+3*M=P := by unfold hd; simp; omega
    have hda : 2^b∣a+(hd j0 m0).x := by
      have H := Nat.dvd_add hP hjcon
      rw [←ha'] at H
      have H' := Nat.dvd_sub H hdiv3M
      simpa using H'
    have hdl : 2^b∣2*(l+(hd j0 m0).y) := by
      have H := Nat.dvd_sub hP (Nat.dvd_add hjcon hdiv3M)
      rw [←hl'] at H
      simpa [Nat.add_assoc,J] using H
    apply runCertAt_sound reach parent forbid f (b-1) a l (hd j0 m0) hdir _ hrp
    constructor
    · exact weaken _ _ _ (by omega) hda
    · apply cancel_pow b 1 _ hb1
      simpa using hdl
  · obtain ⟨n,hn,hpar,ha,hl⟩ := H
    have hpar' : n%2=ho j0 m0 := by rw [hsumpar] at hpar; omega
    have h := List.all_eq_true.mp hhigh n (List.mem_range.mpr (by omega))
    simp only [show n+2≤hv j0 m0 from hn,hpar',and_self,if_true,Bool.and_eq_true] at h
    obtain ⟨hvalid,hcert⟩ := h
    obtain ⟨hA,hK⟩ := of_decide_eq_true hvalid
    have ha' : 2^(n+1)*(a+(hh j0 m0 n).x)=2*j+3+k+ho j0 m0+hq j0 m0 := by
      rw [hsumpar] at ha
      rw [Nat.mul_add] at ha hA ⊢
      rw [Nat.mul_add] at ha
      omega
    have hdiva : 2^(b-(n+1))∣a+(hh j0 m0 n).x := cancel_pow b (n+1) _ (by omega) (ha' ▸ hdivQ)
    have hl' : 2*(l+(hh j0 m0 n).y)+(a+(hh j0 m0 n).x)+6*M=2*P := by omega
    have hdiv : 2^(b-(n+1))∣2*(l+(hh j0 m0 n).y)+(a+(hh j0 m0 n).x) := by
      have H : 2^b∣2*P := Nat.dvd_trans hP (Nat.dvd_mul_left P 2)
      have H' : 2^b∣6*M := Nat.dvd_trans hmcon (Nat.dvd_mul_left M 6)
      rw [←hl'] at H
      have H'' := Nat.dvd_sub H H'
      exact weaken b _ _ (by omega) (by simpa using H'')
    have hdivl : 2^(b-(n+1))∣2*(l+(hh j0 m0 n).y) := by
      have H := Nat.dvd_sub hdiv hdiva
      simpa using H
    apply runCertAt_sound reach parent forbid f (b-(n+2)) a l (hh j0 m0 n) hcert _ hrp
    constructor
    · exact weaken _ _ _ (by omega) hdiva
    · have H := cancel_pow (b-(n+1)) 1 (l+(hh j0 m0 n).y) (by omega) (by simpa using hdivl)
      rwa [show b-(n+1)-1=b-(n+2) by omega] at H

/-- Both actual high indices are unrestricted above their base values. -/
theorem high_cylinder_stop_excluded (f b j0 m0 j m k : Nat)
    (h : highCheckAt f b j0 m0=true)
    (hjj : j0≤j) (hmm : m0≤m) (hb : b≤2*m+2)
    (hjcon : 2^b∣j-j0) (hmcon : 2^b∣m-m0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  apply high_cylinder_exclusion BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f b j0 m0 j m k h hjj hmm hb hjcon hmcon hstop
  intro x y hx hy hr
  obtain ⟨a,k,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp he⟩

#print axioms high_cylinder_exclusion
#print axioms high_cylinder_stop_excluded
end BB6.Agent13HighCylinder
