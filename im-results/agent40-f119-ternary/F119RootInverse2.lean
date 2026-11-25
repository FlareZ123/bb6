import F119
import F119Inverse2

namespace F119RootInverse2
open F119 F119Inverse2

def secondClasses (k : Nat) : Prop := k%60=0 ∨ k%60=3 ∨ k%60=39 ∨ k%60=48
theorem pure_return_arith (p a : Nat) : p+1+a+4-2*1=p+a+3 := by omega

theorem incoming_first_parent {s : Section} (hs : Invariant s) {C k y : Nat}
    (hk : 4≤k) (hc : (C=39 ∧ k%12=0) ∨ (C=33 ∧ k%12=3))
    (hy : 10*y+C=3^(k+2)) (he : Edge s (y,1)) :
    ∃ t r, (r=1 ∨ r=2) ∧ s=(3*(3*t+r),1) ∧
      ((C=39 ∧ ((r=1 ∧ k%60=0) ∨ (r=2 ∧ k%60=48))) ∨
       (C=33 ∧ ((r=1 ∧ k%60=39) ∨ (r=2 ∧ k%60=3)))) := by
  generalize ht : (y,1) = target at he
  cases he with
  | @one x c h t hpos hx =>
    have heq : y=x+c+h+t+2 := congrArg Prod.fst ht
    have hc1 : c=1 := by
      rcases hs.2 with h1|⟨a,ha,hs2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst hs2
        have hc' : c=2 := congrArg Prod.snd hs2
        exact False.elim (no_tag_two_parent C k y a h t 1 (by omega) hk ha (Or.inl rfl)
          (hx'.symm.trans hx) hy (by omega))
    have hEq : rhs C h 1 t=3^(k+2) := by
      unfold rhs
      rw [← hy]
      simp only [Nat.reduceEqDiff, ite_false, Nat.add_zero, Nat.mul_one, Nat.mul_add] at *
      rw [Nat.mul_left_comm (3^h) 3 t] at hx
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    obtain ⟨hh,hg⟩ := second_gate C h 1 t k hc (Or.inl rfl) hEq
    subst h
    exact ⟨t,1,Or.inl rfl,by simp [hx,hc1],hg⟩
  | @two x c h t hx =>
    have heq : y=x+c+h+t+3 := congrArg Prod.fst ht
    have hc1 : c=1 := by
      rcases hs.2 with h1|⟨a,ha,hs2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst hs2
        have hc' : c=2 := congrArg Prod.snd hs2
        exact False.elim (no_tag_two_parent C k y a h t 2 (by omega) hk ha (Or.inr rfl)
          (hx'.symm.trans hx) hy (by omega))
    have hEq : rhs C h 2 t=3^(k+2) := by
      unfold rhs
      rw [← hy]
      simp only [ite_true, Nat.mul_add] at *
      rw [Nat.mul_left_comm (3^h) 3 t] at hx
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    obtain ⟨hh,hg⟩ := second_gate C h 2 t k hc (Or.inr rfl) hEq
    subst h
    exact ⟨t,2,Or.inr rfl,by simp [hx,hc1],hg⟩
  | @power a c r hr hm =>
    have heq : y=3^a+c+a+4-2*r := congrArg Prod.fst ht
    have hr1 : r=1 := (congrArg Prod.snd ht).symm
    have hc1 : c=1 := invariant_power_tag hs rfl
    rw [hc1,hr1] at heq
    have hc2 : C=33 ∨ C=39 := by omega
    have htarget : y=3^a+a+3 := by
      calc
        y = 3^a+1+a+4-2*1 := heq
        _ = 3^a+a+3 := pure_return_arith _ _
    exact False.elim (no_power_parent C k y a hc2 hk hy htarget)

theorem root_first_parent_class {k y C : Nat}
    (hk : 4≤k) (hc : (C=39 ∧ k%12=0) ∨ (C=33 ∧ k%12=3))
    (hy : 10*y+C=3^(k+2)) (hr : MacroReach start (y,1)) : secondClasses k := by
  generalize ht : (y,1)=s at hr
  cases hr with
  | refl =>
    have hy4 : y=4 := congrArg Prod.fst ht
    have hpow : 729≤3^(k+2) := Nat.pow_le_pow_right (n:=3) (by decide) (show 6≤k+2 by omega)
    omega
  | tail hr he =>
    rw [← ht] at he
    obtain ⟨t,r,_,_,hg⟩ := incoming_first_parent (root_invariant hr) hk hc hy he
    unfold secondClasses
    omega

theorem root_second_class {k : Nat} (hk : k%12=0 ∨ k%12=3)
    (hr : MacroReach start (3^k,1)) : secondClasses k := by
  by_cases hsmall : k<4
  · unfold secondClasses
    omega
  generalize ht : (3^k,1)=s at hr
  cases hr with
  | refl => exact False.elim (root_not_power k (congrArg Prod.fst ht).symm)
  | tail hr he =>
    rw [← ht] at he
    rename_i pred
    obtain ⟨_,hc,hp⟩ := incoming_power (root_invariant hr) he
    rcases hp with ⟨h4,t,hx,hy⟩|⟨h4,t,hx,hy⟩
    · have e : 10*pred.1+33=3^(k+2) := by rw [Nat.pow_add,hy,hx]; omega
      have ep : pred=(pred.1,1) := Prod.ext rfl hc
      rw [ep] at hr
      exact root_first_parent_class (by omega) (Or.inr ⟨rfl,by omega⟩) e hr
    · have e : 10*pred.1+39=3^(k+2) := by rw [Nat.pow_add,hy,hx]; omega
      have ep : pred=(pred.1,1) := Prod.ext rfl hc
      rw [ep] at hr
      exact root_first_parent_class (by omega) (Or.inl ⟨rfl,by omega⟩) e hr

theorem root_halts_iff_second_classes : Halts (.D 0 3 1) ↔
    ∃ k, secondClasses k ∧ MacroReach start (3^k,1) := by
  rw [root_halts_iff_restricted_power]
  constructor
  · rintro ⟨k,hk,hr⟩
    exact ⟨k,root_second_class hk hr,hr⟩
  · rintro ⟨k,hk,hr⟩
    unfold secondClasses at hk
    exact ⟨k,by omega,hr⟩

#print axioms root_halts_iff_second_classes
end F119RootInverse2
