import BB429RootMod64R0
import Lean.Elab.Tactic.Omega

namespace BB429RootMod64R2
open BB429NewResidue

set_option maxHeartbeats 20000000
set_option maxRecDepth 16384

/-- At counter 3 and b congruent to 18 (mod32), a source predecessor,
if any, would be a forbidden 0(mod8),1(mod4) source cell. -/
private theorem no_small_three (u w b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (3,b))
    (hb : b%32=18) : False := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed,Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- No true blank-root visit with a%16=3 and b%32=18.
The first source inverse contradicts positive-even 2(mod8).
The other source inverse contradicts global source Allowed. -/
theorem no_3_18 (a b : Nat)
    (hr : Reach a b) (ha : a%16=3) (hb : b%32=18) : False := by
  by_cases hbig : 13≤a
  · rcases odd_back a b hbig (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · rcases hp with ⟨n,hn⟩
      have he : 0<x ∧ x%2=0 := by omega
      have h8 := BB429RootEven8.rooted_positive_even_eight n x y hn he.1 he.2
      omega
    · have hallow := reach_allowed x y hp
      unfold BB429Mod8.Allowed at hallow
      omega
  · have h3 : a=3 := by omega
    subst a
    obtain ⟨x,y,hp,hs⟩ := pred 3 b (by omega) hr
    exact no_small_three x y b (reach_allowed x y hp) hs hb

/-- Nine has no alternative predecessor in this 12-rule accelerator. -/
private theorem nine_predecessor (x y b : Nat)
    (hs : BB429.next (x,y)=some (9,b)) : x=3 ∧ y=b+9 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- No actual blank-source configuration (a%32,b%32)=(9,9). -/
theorem no_9_9 (a b : Nat)
    (hr : Reach a b) (ha : a%32=9) (hb : b%32=9) : False := by
  by_cases hbig : 13≤a
  · rcases odd_back a b hbig (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · exact no_3_18 x y hp (by omega) (by omega)
    · omega
  · have h9 : a=9 := by omega
    subst a
    obtain ⟨x,y,hp,hs⟩ := pred 9 b (by omega) hr
    obtain ⟨hx,hy⟩ := nine_predecessor x y b hs
    exact no_3_18 x y hp (by omega) (by omega)

/-- No actual blank-source configuration (a%64,b%32)=(21,20). -/
theorem no_21_20 (a b : Nat)
    (hr : Reach a b) (ha : a%64=21) (hb : b%32=20) : False := by
  rcases odd_back a b (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · exact no_9_9 x y hp (by omega) (by omega)
  · omega

#print axioms no_small_three
#print axioms nine_predecessor
#print axioms no_3_18
#print axioms no_9_9
#print axioms no_21_20

end BB429RootMod64R2
