import MixedFourNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem pull_unique_one (start : Nat × Nat) (time x y u v : Nat)
    (hu : ∀ a k, secNext (a,k)=some (x,y) → a=u ∧ k=v)
    (h : BB6.Agent8Section.run secNext (time+1) (some start)=some (x,y)) :
    BB6.Agent8Section.run secNext time (some start)=some (u,v) := by
  change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
    some (x,y) at h
  cases hp : BB6.Agent8Section.run secNext time (some start) with
  | none => simp [hp] at h
  | some p =>
      rcases p with ⟨a,k⟩
      have he : secNext (a,k)=some (x,y) := by simpa [hp] using h
      obtain ⟨ha,hk⟩ := hu a k he
      simpa only [ha,hk] using hp

private theorem lift_unique_step (x y u v d : Nat)
    (he : secNext (u,v)=some (x,y))
    (hu : ∀ a k, secNext (a,k)=some (x,y) → a=u ∧ k=v)
    (hf : BB6.Agent8Section.run secNext d
      (some (mixedFourNormalize u v))=some (u,v))
    (hp : ∀ (start : Nat × Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+d) (some start)=some (u,v) →
      BB6.Agent8Section.run secNext time (some start)=
        some (mixedFourNormalize u v)) :
    (BB6.Agent8Section.run secNext (d+1)
      (some (mixedFourNormalize u v))=some (x,y)) ∧
    (∀ (start : Nat × Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+(d+1)) (some start)=some (x,y) →
      BB6.Agent8Section.run secNext time (some start)=
        some (mixedFourNormalize u v)) := by
  constructor
  · change (BB6.Agent8Section.run secNext d
      (some (mixedFourNormalize u v))).bind secNext = some (x,y)
    simpa only [hf,Option.bind_some] using he
  · intro start time hh
    have htop : BB6.Agent8Section.run secNext ((time+d)+1) (some start)=some (x,y) := by
      simpa only [show time+(d+1)=time+d+1 by omega] using hh
    have hprev := pull_unique_one start (time+d) x y u v hu htop
    exact hp start time hprev

private theorem odd_low_edge_exact (x y : Nat) (hg : oddLowGate x y) :
    secNext ((x+y-4)/2,(x+3*y-10)/4)=some (x,y) ∧
    (∀ a k, secNext (a,k)=some (x,y) →
      a=(x+y-4)/2 ∧ k=(x+3*y-10)/4) := by
  rcases hg with ⟨hx,hy,hy5,h4,h16,hsize⟩
  constructor
  · apply (oddodd_lowval_parent_iff _ _ x y hx hy hy5 h4 h16 hsize).mpr
    constructor <;> omega
  · intro a k h
    have hd := (oddodd_lowval_parent_iff a k x y hx hy hy5 h4 h16 hsize).mp h
    omega

private theorem even_seven_edge_exact (x y : Nat) (hg : evenSevenGate x y) :
    secNext ((x+y-5)/2,(x+3*y-9)/4)=some (x,y) ∧
    (∀ a k, secNext (a,k)=some (x,y) →
      a=(x+y-5)/2 ∧ k=(x+3*y-9)/4) := by
  rcases hg with ⟨hx,hy,hy5,hseven,hsize⟩
  constructor
  · apply (odd_seven_parent_iff _ _ x y hx hy hy5 hseven hsize).mpr
    constructor <;> omega
  · intro a k h
    have hd := (odd_seven_parent_iff a k x y hx hy hy5 hseven hsize).mp h
    omega

private theorem even_affine_edge_exact (x y : Nat) (hg : evenAffineGate x y) :
    secNext (x+y-2,(y-2)/2)=some (x,y) ∧
    (∀ a k, secNext (a,k)=some (x,y) →
      a=x+y-2 ∧ k=(y-2)/2) := by
  rcases hg with ⟨hy,he,hs⟩
  constructor
  · exact (BB6.Agent15.section_sum_one_even_iff_affine
      (x+y-2) ((y-2)/2) x y hy he hs).mpr ⟨rfl,rfl⟩
  · intro a k h
    exact (BB6.Agent15.section_sum_one_even_iff_affine
      a k x y hy he hs).mp h

private theorem six_even_edge_exact (x y : Nat)
    (hg : BB6.Agent46.sixEvenRightGate x y) :
    secNext (x+y-2,(y-2)/2)=some (x,y) ∧
    (∀ a k, secNext (a,k)=some (x,y) →
      a=x+y-2 ∧ k=(y-2)/2) := by
  rcases hg with ⟨hy,he,h0,h7⟩
  constructor
  · exact (BB6.Agent46.section_even_right_six_iff
      (x+y-2) ((y-2)/2) x y hy he h0 h7).mpr ⟨rfl,rfl⟩
  · intro a k h
    exact (BB6.Agent46.section_even_right_six_iff
      a k x y hy he h0 h7).mp h

/-- Every pair has a finite canonical source-real forced predecessor chain.
    All arbitrary-start paths reaching the pair after d further steps share
    the same pair d steps previously. The chain length is sharp. -/
theorem mixed_four_all_start_exact_ancestry (x y : Nat) :
    ∃ d : Nat,
      BB6.Agent8Section.run secNext d
        (some (mixedFourNormalize x y))=some (x,y) ∧
      ∀ (start : Nat × Nat) (time : Nat),
        BB6.Agent8Section.run secNext (time+d) (some start)=some (x,y) →
        BB6.Agent8Section.run secNext time (some start)=
          some (mixedFourNormalize x y) := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      by_cases hg : oddLowGate x y
      · let u := (x+y-4)/2
        let v := (x+3*y-10)/4
        have hlt : u+2*v<z := by dsimp [u,v,oddLowGate] at *; omega
        obtain ⟨d,hf,hp⟩ := ih _ hlt u v (by rfl)
        obtain ⟨he,hu⟩ := odd_low_edge_exact x y hg
        have hs := lift_unique_step x y u v d he hu hf hp
        have hn : mixedFourNormalize x y=mixedFourNormalize u v := by
          conv => lhs; unfold mixedFourNormalize
          rw [dif_pos hg]
        refine ⟨d+1,?_,?_⟩
        · simpa only [hn] using hs.1
        · intro start time ht
          rw [hn]
          exact hs.2 start time ht
      · by_cases hg7 : evenSevenGate x y
        · let u := (x+y-5)/2
          let v := (x+3*y-9)/4
          have hlt : u+2*v<z := by
            dsimp [u,v,evenSevenGate] at *; omega
          obtain ⟨d,hf,hp⟩ := ih _ hlt u v (by rfl)
          obtain ⟨he,hu⟩ := even_seven_edge_exact x y hg7
          have hs := lift_unique_step x y u v d he hu hf hp
          have hn : mixedFourNormalize x y=mixedFourNormalize u v := by
            conv => lhs; unfold mixedFourNormalize
            rw [dif_neg hg,dif_pos hg7]
          refine ⟨d+1,?_,?_⟩
          · simpa only [hn] using hs.1
          · intro start time ht
            rw [hn]
            exact hs.2 start time ht
        · by_cases hga : evenAffineGate x y
          · let u := x+y-2
            let v := (y-2)/2
            have hlt : u+2*v<z := by
              dsimp [u,v,evenAffineGate] at *; omega
            obtain ⟨d,hf,hp⟩ := ih _ hlt u v (by rfl)
            obtain ⟨he,hu⟩ := even_affine_edge_exact x y hga
            have hs := lift_unique_step x y u v d he hu hf hp
            have hn : mixedFourNormalize x y=mixedFourNormalize u v := by
              conv => lhs; unfold mixedFourNormalize
              rw [dif_neg hg,dif_neg hg7,dif_pos hga]
            refine ⟨d+1,?_,?_⟩
            · simpa only [hn] using hs.1
            · intro start time ht
              rw [hn]
              exact hs.2 start time ht
          · by_cases hgs : BB6.Agent46.sixEvenRightGate x y
            · let u := x+y-2
              let v := (y-2)/2
              have hlt : u+2*v<z := by
                dsimp [u,v,BB6.Agent46.sixEvenRightGate] at *
                omega
              obtain ⟨d,hf,hp⟩ := ih _ hlt u v (by rfl)
              obtain ⟨he,hu⟩ := six_even_edge_exact x y hgs
              have hs := lift_unique_step x y u v d he hu hf hp
              have hn : mixedFourNormalize x y=mixedFourNormalize u v := by
                conv => lhs; unfold mixedFourNormalize
                rw [dif_neg hg,dif_neg hg7,dif_neg hga,dif_pos hgs]
              refine ⟨d+1,?_,?_⟩
              · simpa only [hn] using hs.1
              · intro start time ht
                rw [hn]
                exact hs.2 start time ht
            · have hn : mixedFourNormalize x y=(x,y) := by
                unfold mixedFourNormalize
                rw [dif_neg hg,dif_neg hg7,dif_neg hga,dif_neg hgs]
              refine ⟨0,?_,?_⟩
              · simpa only [hn,BB6.Agent8Section.run] using
                  (rfl : some (x,y)=some (x,y))
              · intro start time ht
                simpa only [Nat.add_zero,hn] using ht

#print axioms mixed_four_all_start_exact_ancestry
end BB6.Agent3
