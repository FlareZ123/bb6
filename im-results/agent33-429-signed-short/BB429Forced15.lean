import BB429NewResidue
import BB429RootMod16

namespace BB429Forced15
open BB429NewResidue
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-!
# Full original-root exclusion of the 15-line q=1(mod4) cylinder.

In contrast to a signed affine simulation, the proof uses the exact inverse
theorems of the blank-start BB429 accelerator and only two previously
established authentic invariants (BB429Mod8.Allowed and the positive-even
eight-gate). All natural t>=1 are covered uniformly, at arbitrary run times.
-/

/-- The first three authentic inverse steps are necessarily F E F. -/
theorem three_forced_FEF (t : Nat) (ht : 1 ≤ t)
    (hr : Reach (128*t+47) (256*t+91)) :
    Reach (80*t+25) (352*t+122) := by
  have h1 : Reach (64*t+22) (384*t+138) := by
    rcases odd_back (128*t+47) (256*t+91)
        (by omega) (by omega) hr with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hmod⟩
    · have hxa : x=64*t+22 := by omega
      have hya : y=384*t+138 := by omega
      rw [hxa,hya] at hp
      exact hp
    · omega
  have h2 : Reach (160*t+53) (192*t+69) := by
    obtain ⟨x,y,hp,hx,hy,hmod⟩ :=
      even_back (64*t+22) (384*t+138)
        (by omega) (by omega) h1
    have hxa : x=160*t+53 := by omega
    have hya : y=192*t+69 := by omega
    rw [hxa,hya] at hp
    exact hp
  rcases odd_back (160*t+53) (192*t+69)
      (by omega) (by omega) h2 with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hmod⟩
  · have hxa : x=80*t+25 := by omega
    have hya : y=352*t+122 := by omega
    rw [hxa,hya] at hp
    exact hp
  · omega

/-- No positive parameter in the true 15-line q=1(mod4) cylinder is
    reachable from the blank accelerator. This is uniform in time. -/
theorem rooted_15_q1_mod4_excluded (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (128*t+47) (256*t+91) := by
  intro hroot
  have h3 := three_forced_FEF t ht hroot
  rcases odd_back (80*t+25) (352*t+122)
      (by omega) (by omega) h3 with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hmod⟩
  · have hxa : x=40*t+11 := by omega
    have hya : y=432*t+147 := by omega
    rw [hxa,hya] at hp
    rcases odd_back (40*t+11) (432*t+147)
        (by omega) (by omega) hp with
      ⟨z,w,hp2,hz,hw⟩ | ⟨z,w,hp2,hz,hw,hmod2⟩
    · obtain ⟨n,hn⟩ := hp2
      have hw8 : w%8=2 :=
        BB429RootEven8.rooted_positive_even_eight n z w hn
          (by omega) (by omega)
      omega
    · omega
  · have hxa : x=168*t+49 := by omega
    have hya : y=176*t+63 := by omega
    rw [hxa,hya] at hp
    have hallow := BB429NewResidue.reach_allowed
      (168*t+49) (176*t+63) hp
    unfold BB429Mod8.Allowed at hallow
    omega

#print axioms three_forced_FEF
#print axioms rooted_15_q1_mod4_excluded
end BB429Forced15
