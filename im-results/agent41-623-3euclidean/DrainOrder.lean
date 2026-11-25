import Lean

namespace BB6.Agent41DrainOrder

variable {σ : Type} (B : Nat → Nat → Nat → Option σ) (D : Nat → Nat → σ)

structure FlatLaws : Prop where
  inj : ∀ a z x y, D a z = D x y → a= x ∧ z= y
  zero : ∀ a z, B a 0 z = some (D a z)
  r0 : ∀ a q z, 0 < q → B a (3*q) z = B (a+1) (q-1) (z+6*q+3)
  r1 : ∀ a q z, 0 < a → B a (3*q+1) z = B (a-1) q (z+6*q+7)
  r10 : ∀ q z, B 0 (3*q+1) z = none
  r2 : ∀ a q z, 0 < a → B a (3*q+2) z = B (a-1) (q+1) (z+6*q+5)
  r20 : ∀ q z, B 0 (3*q+2) z = B 0 q (z+6*q+7)

/-- Comparison independent of the initial third coordinate. -/
def SameAt (b : Nat) : Prop :=
  ∀ a z w x y X Y,
    B a b z= some (D x y) → B a b w= some (D X Y) →
    x= X ∧ y+w= Y+z

/-- Strict lexicographic order of (third,first) output as the first input
increases. The third-coordinate jump has a sharp uniform affine bound. -/
def MonoAt (b : Nat) : Prop :=
  ∀ a c z w x y X Y, a< c →
    B a b z= some (D x y) → B c b w= some (D X Y) →
    y+w≤ Y+z ∧ Y+z+2≤ y+w+4*(c-a) ∧
    (y+w= Y+z → X+a= x+c)

/-- Cross-block control. These bounds are not unconditional monotonicity
in b: their dependence on the input first counters is essential. -/
def AdjAt (b : Nat) : Prop :=
  ∀ a c z w x y X Y,
    B a b z= some (D x y) → B c (b+1) w= some (D X Y) →
    (if a=0 then y+w+2≤ Y+z else y+w+4≤ Y+z+4*a) ∧
    Y+z≤ y+w+4*c+4 ∧
    (a=0 → Y+z= y+w+2 → X= x+c+1)

theorem sameAt (h : FlatLaws B D) (b : Nat) : SameAt B D b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a z w x y X Y hz hw
    by_cases hb : b=0
    · subst b
      rw [h.zero] at hz hw
      obtain ⟨hx,hy⟩ := h.inj _ _ _ _ (Option.some.inj hz)
      obtain ⟨hX,hY⟩ := h.inj _ _ _ _ (Option.some.inj hw)
      omega
    · let q := b/3
      have hr : b=3*q ∨ b=3*q+1 ∨ b=3*q+2 := by dsimp [q]; omega
      rcases hr with hr|hr|hr
      · have hq : 0 < q := by omega
        rw [hr,h.r0 _ _ _ hq] at hz hw
        have H := ih (q-1) (by omega) _ _ _ _ _ _ _ hz hw
        omega
      · by_cases ha : a=0
        · subst a; rw [hr,h.r10] at hz; contradiction
        · rw [hr,h.r1 _ _ _ (by omega)] at hz hw
          have H := ih q (by omega) _ _ _ _ _ _ _ hz hw
          omega
      · by_cases ha : a=0
        · subst a; rw [hr,h.r20] at hz hw
          have H := ih q (by omega) _ _ _ _ _ _ _ hz hw
          omega
        · rw [hr,h.r2 _ _ _ (by omega)] at hz hw
          have H := ih (q+1) (by omega) _ _ _ _ _ _ _ hz hw
          omega

theorem comparison (h : FlatLaws B D) (b : Nat) :
    MonoAt B D b ∧ AdjAt B D b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    constructor
    · intro a c z w x y X Y hac hz hw
      by_cases hb : b=0
      · subst b
        rw [h.zero] at hz hw
        obtain ⟨hx,hy⟩ := h.inj _ _ _ _ (Option.some.inj hz)
        obtain ⟨hX,hY⟩ := h.inj _ _ _ _ (Option.some.inj hw)
        omega
      · let q := b/3
        have hr : b=3*q ∨ b=3*q+1 ∨ b=3*q+2 := by dsimp [q]; omega
        rcases hr with hr|hr|hr
        · have hq : 0 < q := by omega
          rw [hr,h.r0 _ _ _ hq] at hz hw
          have H := (ih (q-1) (by omega)).1 _ _ _ _ _ _ _ _ (by omega) hz hw
          obtain ⟨hlo,hhi,heq⟩ := H
          refine ⟨by omega,by omega,?_⟩
          intro hh
          have he := heq (by omega)
          omega
        · by_cases ha : a=0
          · subst a; rw [hr,h.r10] at hz; contradiction
          · rw [hr,h.r1 _ _ _ (by omega)] at hz hw
            have H := (ih q (by omega)).1 _ _ _ _ _ _ _ _ (by omega) hz hw
            obtain ⟨hlo,hhi,heq⟩ := H
            refine ⟨by omega,by omega,?_⟩
            intro hh
            have he := heq (by omega)
            omega
        · by_cases ha : a=0
          · subst a
            rw [hr,h.r20] at hz
            rw [hr,h.r2 _ _ _ (by omega)] at hw
            have H := (ih q (by omega)).2 _ _ _ _ _ _ _ _ hz hw
            simp at H
            obtain ⟨hlo,hhi,heq⟩ := H
            refine ⟨by omega,by omega,?_⟩
            intro hh
            have he := heq (by omega)
            omega
          · rw [hr,h.r2 _ _ _ (by omega)] at hz hw
            have H := (ih (q+1) (by omega)).1 _ _ _ _ _ _ _ _ (by omega) hz hw
            obtain ⟨hlo,hhi,heq⟩ := H
            refine ⟨by omega,by omega,?_⟩
            intro hh
            have he := heq (by omega)
            omega
    · intro a c z w x y X Y hz hw
      by_cases hb : b=0
      · subst b
        rw [h.zero] at hz
        obtain ⟨hx,hy⟩ := h.inj _ _ _ _ (Option.some.inj hz)
        by_cases hc : c=0
        · subst c; rw [show 0+1=3*0+1 by decide,h.r10] at hw; contradiction
        · rw [show 0+1=3*0+1 by decide,h.r1 _ _ _ (by omega),h.zero] at hw
          obtain ⟨hX,hY⟩ := h.inj _ _ _ _ (Option.some.inj hw)
          refine ⟨?_,by omega,?_⟩
          · split <;> omega
          · intro ha he; omega
      · let q := b/3
        have hr : b=3*q ∨ b=3*q+1 ∨ b=3*q+2 := by dsimp [q]; omega
        rcases hr with hr|hr|hr
        · have hq : 0 < q := by omega
          rw [hr,h.r0 _ _ _ hq] at hz
          rw [show b+1=3*q+1 by omega] at hw
          by_cases hc : c=0
          · subst c; rw [h.r10] at hw; contradiction
          · rw [h.r1 _ _ _ (by omega)] at hw
            have hq' : q-1+1= q := by omega
            rw [← hq'] at hw
            obtain ⟨hlo,hhi,heq⟩ := (ih (q-1) (by omega)).2 _ _ _ _ _ _ _ _ hz hw
            simp only [if_neg (show a+1≠0 by omega)] at hlo
            refine ⟨?_,by omega,?_⟩
            · split <;> omega
            · intro ha he; omega
        · have ha : a≠0 := by
            intro h0; subst a; rw [hr,h.r10] at hz; contradiction
          rw [hr,h.r1 _ _ _ (by omega)] at hz
          rw [show b+1=3*q+2 by omega] at hw
          by_cases hc : c=0
          · subst c; rw [h.r20] at hw
            by_cases ha1 : a=1
            · subst a
              have H := sameAt B D h q 0 _ _ _ _ _ _ hz hw
              simp only [if_neg (by decide : (1:Nat)≠0)]
              omega
            · obtain ⟨hlo,hhi,heq⟩ := (ih q (by omega)).1 0 (a-1) _ _ _ _ _ _ (by omega) hw hz
              simp only [if_neg ha]
              omega
          · rw [h.r2 _ _ _ (by omega)] at hw
            obtain ⟨hlo,hhi,heq⟩ := (ih q (by omega)).2 _ _ _ _ _ _ _ _ hz hw
            refine ⟨?_,by omega,?_⟩
            · rw [if_neg ha]; split at hlo <;> omega
            · intro h0; contradiction
        · rw [show b+1=3*(q+1) by omega,h.r0 _ _ _ (by omega)] at hw
          have hq' : q+1-1= q := by omega
          rw [hq'] at hw
          by_cases ha : a=0
          · subst a; rw [hr,h.r20] at hz
            obtain ⟨hlo,hhi,heq⟩ := (ih q (by omega)).1 0 (c+1) _ _ _ _ _ _ (by omega) hz hw
            simp
            refine ⟨by omega,by omega,?_⟩
            intro he
            have hh := heq (by omega)
            omega
          · rw [hr,h.r2 _ _ _ (by omega)] at hz
            obtain ⟨hlo,hhi,heq⟩ := (ih q (by omega)).2 _ _ _ _ _ _ _ _ hw hz
            simp only [if_neg (show c+1≠0 by omega)] at hlo
            simp only [if_neg ha]
            refine ⟨by omega,by omega,?_⟩
            intro h0; contradiction

theorem fixed_block_injective (h : FlatLaws B D)
    (b a c z x y : Nat) (ha : B a b z= some (D x y))
    (hc : B c b z= some (D x y)) : a= c := by
  by_cases hlt : a< c
  · obtain ⟨_,_,he⟩ := (comparison B D h b).1 _ _ _ _ _ _ _ _ hlt ha hc
    have := he rfl
    omega
  · by_cases hgt : c< a
    · obtain ⟨_,_,he⟩ := (comparison B D h b).1 _ _ _ _ _ _ _ _ hgt hc ha
      have := he rfl
      omega
    · omega

#print axioms sameAt
#print axioms comparison
#print axioms fixed_block_injective

end BB6.Agent41DrainOrder
