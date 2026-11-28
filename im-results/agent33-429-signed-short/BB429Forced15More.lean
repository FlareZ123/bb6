import BB429Forced13More
import BB429Forced15

namespace BB429Forced15More
open BB429NewResidue BB429Forced13More

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-!
# Another entire genuine-root 15-line cylinder: q=2(mod8).

The forced prefix F E F ends at a two-branch node. Its S child is
forbidden after one F by the positive-even source invariant; its F child
is forbidden after three further forced F's. No signed finite-precision
assumptions or fixed-size computation are used.
-/

theorem rooted_15_q2_mod8_excluded (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+79) (512*t+155) := by
  intro hroot
  have h1raw := forced_F (256*t+79) (512*t+155) (128*t+38)
    (by omega) (by omega) (by omega) (by omega) hroot
  have hy1 : (512*t+155)+(256*t+79)=768*t+234 := by omega
  rw [hy1] at h1raw
  have h2 : Reach (320*t+93) (384*t+117) :=
    forced_E (128*t+38) (768*t+234) (320*t+93) (384*t+117)
      (by omega) (by omega) (by omega) (by omega) h1raw
  have h3raw := forced_F (320*t+93) (384*t+117) (160*t+45)
    (by omega) (by omega) (by omega) (by omega) h2
  have hy3 : (384*t+117)+(320*t+93)=704*t+210 := by omega
  rw [hy3] at h3raw
  rcases odd_back (160*t+45) (704*t+210)
      (by omega) (by omega) h3raw with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
  · have hxa : x=80*t+21 := by omega
    have hya : y=864*t+255 := by omega
    rw [hxa,hya] at hp
    have h5 := forced_F (80*t+21) (864*t+255) (40*t+9)
      (by omega) (by omega) (by omega) (by omega) hp
    have hy5 : (864*t+255)+(80*t+21)=944*t+276 := by omega
    rw [hy5] at h5
    have h6 := forced_F (40*t+9) (944*t+276) (20*t+3)
      (by omega) (by omega) (by omega) (by omega) h5
    have hy6 : (944*t+276)+(40*t+9)=984*t+285 := by omega
    rw [hy6] at h6
    have h7 := forced_F (20*t+3) (984*t+285) (10*t)
      (by omega) (by omega) (by omega) (by omega) h6
    have hy7 : (984*t+285)+(20*t+3)=1004*t+288 := by omega
    rw [hy7] at h7
    obtain ⟨n,hn⟩ := h7
    have hgate := BB429RootEven8.rooted_positive_even_eight
      n (10*t) (1004*t+288) hn (by omega) (by omega)
    omega
  · have hxa : x=336*t+91 := by omega
    have hya : y=352*t+107 := by omega
    rw [hxa,hya] at hp
    have h5 := forced_F (336*t+91) (352*t+107) (168*t+44)
      (by omega) (by omega) (by omega) (by omega) hp
    have hy5 : (352*t+107)+(336*t+91)=688*t+198 := by omega
    rw [hy5] at h5
    obtain ⟨n,hn⟩ := h5
    have hgate := BB429RootEven8.rooted_positive_even_eight
      n (168*t+44) (688*t+198) hn (by omega) (by omega)
    omega

/-- Combined necessary mod8 classification, still without an assertion
    that any of the surviving classes are actually blank-reachable. -/
theorem rooted_15_q_mod8_necessary (q : Nat) (hq : 16 ≤ q)
    (hr : Reach (32*q+15) (64*q+27)) :
    q%8=0 ∨ q%8=3 ∨ q%8=4 ∨ q%8=6 ∨ q%8=7 := by
  have hn1 : q%4≠1 := by
    intro h
    let t := q/4
    have ht : 1≤t := by dsimp [t]; omega
    have ha : 32*q+15=128*t+47 := by dsimp [t]; omega
    have hb : 64*q+27=256*t+91 := by dsimp [t]; omega
    rw [ha,hb] at hr
    exact BB429Forced15.rooted_15_q1_mod4_excluded t ht hr
  have hn2 : q%8≠2 := by
    intro h
    let t := q/8
    have ht : 1≤t := by dsimp [t]; omega
    have ha : 32*q+15=256*t+79 := by dsimp [t]; omega
    have hb : 64*q+27=512*t+155 := by dsimp [t]; omega
    rw [ha,hb] at hr
    exact rooted_15_q2_mod8_excluded t ht hr
  omega

#print axioms rooted_15_q2_mod8_excluded
#print axioms rooted_15_q_mod8_necessary
end BB429Forced15More
