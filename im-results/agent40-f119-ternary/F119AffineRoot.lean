import F119
import F119AffineInverse

namespace F119AffineRoot
open F119 F119AffineInverse

private theorem pure_return_arith (p a : Nat) : p+1+a+4-2*1=p+a+3 := by omega

-- Exceptional sources with exponent a below the uniform cutoff A are small.
def maxExceptional (A : Nat) : Nat := 2*3^A+3*A+7

theorem small_power_return (a A : Nat) (ha : a<A) : 3^a+a+3≤maxExceptional A := by
  have hp := Nat.pow_le_pow_right (n:=3) (by decide) (show a≤A by omega)
  unfold maxExceptional
  omega

theorem small_tag_two_return (a A h t r y : Nat) (ha : 2≤a) (hA : a<A)
    (hr : r=1 ∨ r=2) (hx : 3^a+a+1=3^h*(3*t+r))
    (hy : y=3^a+a+1+2+h+t+r+1) : y≤maxExceptional A := by
  have hbound := tag_two_bound a h t r ha hr hx
  have hp := Nat.pow_le_pow_right (n:=3) (by decide) (show a≤A by omega)
  have ht : 3*t+r≤3^a+a+1 := by
    rw [hx]
    exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  unfold maxExceptional
  omega

-- A positive target equation plus a large enough power of 3 excludes
-- every exceptional root-compatible source, including the finite low-a cases.
theorem no_exception_power (D C A a N : Nat) (hD : 0<D) (hA : 2≤A)
    (hbudget : budget D C A<3^A) (hN : D*maxExceptional A+C<3^N) :
    D*(3^a+a+3)+C≠3^N := by
  by_cases ha : A≤a
  · apply no_pure_power D C a N hD
    have hb := exception_cutoff D C A a (by omega) ha hbudget
    have hp := pure_le_budget D C a (by omega)
    omega
  · intro he
    have hsmall := small_power_return a A (by omega)
    have hmul := Nat.mul_le_mul_left D hsmall
    omega

theorem no_exception_tag_two (D C A a h t r y N : Nat) (hD : 0<D) (hA : 2≤A)
    (hbudget : budget D C A<3^A) (hN : D*maxExceptional A+C<3^N)
    (ha : 2≤a) (hr : r=1 ∨ r=2) (hx : 3^a+a+1=3^h*(3*t+r))
    (hy : y=3^a+a+1+2+h+t+r+1) : D*y+C≠3^N := by
  by_cases ha' : A≤a
  · exact no_tag_two D C a h t r y N hD ha hr hx hy
      (exception_cutoff D C A a (by omega) ha' hbudget)
  · intro he
    have hsmall := small_tag_two_return a A h t r y ha (by omega) hr hx hy
    have hmul := Nat.mul_le_mul_left D hsmall
    omega

-- Exact arithmetic branch data, sufficient for an actual macro edge.
def Branch (s : Section) (y H : Nat) : Prop :=
  ∃ h r t, h<H ∧ (r=1 ∨ r=2) ∧ (r=1 → 0<t) ∧
    s=(3^h*(3*t+r),1) ∧ y=generic h r t

theorem branch_edge {s : Section} {y H : Nat} (hb : Branch s y H) : Edge s (y,1) := by
  obtain ⟨h,r,t,_,hr,ht,hs,hy⟩ := hb
  rcases hr with rfl|rfl
  · have hg : y=3^h*(3*t+1)+1+h+t+2 := by
      rw [hy]; unfold generic
      simp only [Nat.reduceEqDiff,ite_false,Nat.add_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul]
      rw [Nat.mul_left_comm (3^h) 3 t, Nat.mul_assoc 3 (3^h) t]
      omega
    rw [hs,hg]
    exact Edge.one (ht rfl) rfl
  · have hg : y=3^h*(3*t+2)+1+h+t+3 := by
      rw [hy]; unfold generic
      simp only [ite_true,Nat.mul_add,Nat.add_mul]
      rw [Nat.mul_left_comm (3^h) 3 t, Nat.mul_assoc 3 (3^h) t]
      omega
    rw [hs,hg]
    exact Edge.two rfl

-- Complete finite inverse theorem for arbitrary affine exponential targets.
theorem edge_iff_branch {s : Section} {y D C N H A : Nat}
    (hs : Invariant s) (hD : 0<D) (hD3 : D%3≠0)
    (hH : 2≤H) (hgap : 2*(C+D*(H+4))<3^H)
    (hA : 2≤A) (hbudget : budget D C A<3^A)
    (hN : D*maxExceptional A+C<3^N) (hy : D*y+C=3^N) :
    Edge s (y,1) ↔ Branch s y H := by
  refine ⟨?_,branch_edge⟩
  intro he
  generalize ht : (y,1)=target at he
  cases he with
  | @one x c h t hpos hx =>
    have heq : y=x+c+h+t+2 := congrArg Prod.fst ht
    have hc : c=1 := by
      rcases hs.2 with h1|⟨a,ha,h2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst h2
        have hc' : c=2 := congrArg Prod.snd h2
        exact False.elim (no_exception_tag_two D C A a h t 1 y N hD hA hbudget hN ha
          (Or.inl rfl) (hx'.symm.trans hx) (by omega) hy)
    have hg : y=generic h 1 t := by
      rw [heq,hc,hx]
      unfold generic
      simp only [Nat.reduceEqDiff,ite_false,Nat.add_zero,Nat.mul_one,Nat.mul_add,Nat.add_mul]
      rw [Nat.mul_left_comm (3^h) 3 t, Nat.mul_assoc 3 (3^h) t]
      omega
    have hlt : h<H := by
      apply Nat.lt_of_not_ge
      intro hn
      exact high_excluded D C h 1 t N hD hD3 (by omega) (Or.inl rfl)
        (generic_cutoff D C H h hn hgap) (hg ▸ hy)
    exact ⟨h,1,t,hlt,Or.inl rfl,fun _ => hpos,by simp [hx,hc],hg⟩
  | @two x c h t hx =>
    have heq : y=x+c+h+t+3 := congrArg Prod.fst ht
    have hc : c=1 := by
      rcases hs.2 with h1|⟨a,ha,h2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst h2
        have hc' : c=2 := congrArg Prod.snd h2
        exact False.elim (no_exception_tag_two D C A a h t 2 y N hD hA hbudget hN ha
          (Or.inr rfl) (hx'.symm.trans hx) (by omega) hy)
    have hg : y=generic h 2 t := by
      rw [heq,hc,hx]
      unfold generic
      simp only [ite_true,Nat.mul_add,Nat.add_mul]
      rw [Nat.mul_left_comm (3^h) 3 t, Nat.mul_assoc 3 (3^h) t]
      omega
    have hlt : h<H := by
      apply Nat.lt_of_not_ge
      intro hn
      exact high_excluded D C h 2 t N hD hD3 (by omega) (Or.inr rfl)
        (generic_cutoff D C H h hn hgap) (hg ▸ hy)
    exact ⟨h,2,t,hlt,Or.inr rfl,by omega,by simp [hx,hc],hg⟩
  | @power a c r hr hm =>
    have heq : y=3^a+c+a+4-2*r := congrArg Prod.fst ht
    have hr1 : r=1 := (congrArg Prod.snd ht).symm
    have hc : c=1 := invariant_power_tag hs rfl
    rw [hc,hr1] at heq
    have he' : y=3^a+a+3 := by
      calc
        y = 3^a+1+a+4-2*1 := heq
        _ = 3^a+a+3 := pure_return_arith _ _
    exact False.elim (no_exception_power D C A a N hD hA hbudget hN (he' ▸ hy))

#print axioms edge_iff_branch
end F119AffineRoot
