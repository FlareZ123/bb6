import NegativeShadow
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13HighShadow
open BB6.Agent13AffineCone BB6.Agent13NegativeShadow BB6.Agent46

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


def runCertAt (f b : Nat) (s : Pair) : Bool :=
  match build f s {} with
  | none => false
  | some (r,c) => decide (r≤b) && certOK c && c[key s]? == some r

theorem runCertAt_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f b x y : Nat) (s : Pair) (h : runCertAt f b s=true) (hc : congruent b x y s) : ¬reach x y := by
  cases he : build f s {} with
  | none => simp [runCertAt,he] at h
  | some p =>
    rcases p with ⟨r,c⟩
    simp only [runCertAt,he,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
    exact cert_sound reach parent forbid c h.1.2 r x y s h.2
      ⟨weaken _ _ _ h.1.1 hc.1,weaken _ _ _ h.1.1 hc.2⟩

def hs (j m : Nat) := 3*m+2-j
def ho (j m : Nat) := hs j m % 2
def hq (j m : Nat) := hs j m - ho j m
def hv (j m : Nat) := v2Aux ((hq j m).log2+1) (hq j m)
def hd (j m : Nat) : Pair := ⟨hs j m+2,(j+3*m+7)/2⟩
def hh (j m n : Nat) : Pair :=
  let a := hq j m / 2^(n+1)+2+ho j m
  ⟨a,(6*m+14+3*n-a)/2⟩
def goodHi (j m n : Nat) : Bool := decide (
  2^(n+1)*(hh j m n).x=hq j m+2^(n+1)*(2+ho j m) ∧
  2*(hh j m n).y+(hh j m n).x=6*m+14+3*n)
def highCheck (f j m : Nat) : Bool :=
  let b := 2*m+2
  let v := hv j m
  decide (2≤j ∧ j≤3*m ∧ 1≤m ∧ v+1≤b ∧ hq j m % 2^(v+1)=2^v ∧ hq j m < 2^b) &&
  (if (j+3*m+5)%2=0 then runCertAt f (b-1) (hd j m) else true) &&
  (List.range (v+1)).all (fun n => if n+2≤v ∧ n%2=ho j m then
    goodHi j m n && runCertAt f (b-(n+2)) (hh j m n) else true)

private theorem pow_bound (m : Nat) : 4*m+4≤(2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    change 4*(m+1)+4≤2^(2*m+2)*4
    omega

theorem high_shadow_exclusion (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f j m k : Nat) (h : highCheck f j m=true)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬reach (2*j+3) k := by
  simp only [highCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hj,hjm,hm,hvb,hvmod,hqbound⟩,hdir⟩,hhigh⟩ := h
  let b := 2*m+2
  let v := hv j m
  let P := 2^b*(j+3)
  have hP : 2^b∣P := ⟨j+3,rfl⟩
  have hP2 : P%2=0 := Nat.mod_eq_zero_of_dvd (weaken b 1 P (by dsimp [b]; omega) hP)
  have hPb : 5*2^b≤P := by
    dsimp [P]
    rw [Nat.mul_comm 5]
    exact Nat.mul_le_mul_left _ (by omega)
  have hbnd : 4*m+4≤2^b := pow_bound m
  have hbnd16 : 16≤2^b := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by dsimp [b]; omega : 4≤b)
  change k+j+3*m+5=P at hstop
  have hk8 : 8≤k := by omega
  have hsumpar : (2*j+3+k)%2=ho j m := by unfold ho hs; omega
  have hsum : 2*j+3+k+ho j m+hq j m=P := by unfold hq hs ho; omega
  have hpow : 2^(v+1)=2*2^v := by rw [Nat.pow_succ,Nat.mul_comm]
  have hmod : (2*j+3+k+(2*j+3+k)%2)%2^(v+1)=2^v := by
    rw [hsumpar,hpow]
    change hq j m % 2^(v+1)=2^v at hvmod
    rw [hpow] at hvmod
    apply complement_half _ _ _ (Nat.pow_pos (by decide)) hvmod
    rw [hsum,←hpow]
    exact weaken b (v+1) P hvb hP
  have hgt : 2^v<2*j+3+k+(2*j+3+k)%2 := by
    have hle : 2^v≤2^b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hsumpar]
    omega
  intro hr
  obtain ⟨a,l,hrp,hp⟩ := parent _ _ (by omega) hk8 hr
  rcases parent_equations a l (2*j+3) k v hk8 hmod hgt hp with H|H
  · obtain ⟨hke,ha,hl⟩ := H
    have hpar : (j+3*m+5)%2=0 := by omega
    simp only [hpar,if_true] at hdir
    have ha' : a+(hd j m).x=P := by unfold hd hs; simp; omega
    have hl' : 2*(l+(hd j m).y)=P := by unfold hd; simp; omega
    apply runCertAt_sound reach parent forbid f (b-1) a l (hd j m) hdir _ hrp
    constructor
    · rw [ha']; exact weaken b _ _ (by omega) hP
    · apply cancel_pow b 1 _ (by dsimp [b]; omega)
      rw [Nat.pow_one,hl']; exact hP
  · obtain ⟨n,hn,hpar,ha,hl⟩ := H
    have hpar' : n%2=ho j m := by rw [hsumpar] at hpar; omega
    have h := List.all_eq_true.mp hhigh n (List.mem_range.mpr (by omega))
    simp only [show n+2≤hv j m from hn,hpar',and_self,if_true,Bool.and_eq_true] at h
    obtain ⟨hvalid,hcert⟩ := h
    obtain ⟨hA,hK⟩ := of_decide_eq_true hvalid
    have ha' : 2^(n+1)*(a+(hh j m n).x)=P := by
      rw [hsumpar] at ha
      rw [Nat.mul_add] at ha hA ⊢
      rw [Nat.mul_add] at ha
      omega
    have hdiva : 2^(b-(n+1))∣a+(hh j m n).x := cancel_pow b (n+1) _ (by omega) (ha' ▸ hP)
    have hl' : 2*(l+(hh j m n).y)+(a+(hh j m n).x)=2*P := by omega
    have hdiv : 2^(b-(n+1))∣2*(l+(hh j m n).y)+(a+(hh j m n).x) := by
      rw [hl']; exact Nat.dvd_trans (weaken b _ _ (by omega) hP) (Nat.dvd_mul_left P 2)
    have hdivl : 2^(b-(n+1))∣2*(l+(hh j m n).y) := by
      have H := Nat.dvd_sub hdiv hdiva
      simpa using H
    apply runCertAt_sound reach parent forbid f (b-(n+2)) a l (hh j m n) hcert _ hrp
    constructor
    · exact weaken _ _ _ (by omega) hdiva
    · have H := cancel_pow (b-(n+1)) 1 (l+(hh j m n).y) (by omega) (by simpa using hdivl)
      rwa [show b-(n+1)-1=b-(n+2) by omega] at H

theorem high_shadow_stop_excluded (f j m k : Nat)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (h : highCheck f j m=true) : ¬ BB6.Agent3.CReach (2*j+3) k := by
  apply high_shadow_exclusion BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f j m k h hstop
  intro x y hx hy hr
  obtain ⟨a,k,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp he⟩

#print axioms runCertAt_sound
#print axioms high_shadow_exclusion
#print axioms high_shadow_stop_excluded
end BB6.Agent13HighShadow
