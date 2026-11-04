import BB429No1021Six
import BB429LowOddMod8
import Lean.Elab.Tactic.Omega

namespace BB429RootMod64R0
open BB429NewResidue

set_option maxHeartbeats 15000000
set_option maxRecDepth 16384

/-- Source root can never encounter the mod16/32 cell (15,26).
Both exact odd predecessors violate previously root-proven invariants. -/
theorem no_15_26 (a b : Nat)
    (hr : Reach a b) (ha : a%16=15) (hb : b%32=26) : False := by
  rcases odd_back a b (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · rcases hp with ⟨n,hn⟩
    have he : 0<x ∧ x%2=0 := by omega
    have h8 := BB429RootEven8.rooted_positive_even_eight n x y hn he.1 he.2
    omega
  · rcases hp with ⟨n,hn⟩
    have h77 := BB429RootMod16.rooted_not_7_7 n x y hn (by omega)
    omega

/-- Source root can never encounter the mod32/32 cell (15,24).
Other odd predecessor is arithmetically impossible; first violates even8. -/
theorem no_15_24 (a b : Nat)
    (hr : Reach a b) (ha : a%32=15) (hb : b%32=24) : False := by
  rcases odd_back a b (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · rcases hp with ⟨n,hn⟩
    have he : 0<x ∧ x%2=0 := by omega
    have h8 := BB429RootEven8.rooted_positive_even_eight n x y hn he.1 he.2
    omega
  · omega

/-- Source root can never encounter the mod32/32 cell (31,24). -/
theorem no_31_24 (a b : Nat)
    (hr : Reach a b) (ha : a%32=31) (hb : b%32=24) : False := by
  rcases odd_back a b (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · rcases hp with ⟨n,hn⟩
    have he : 0<x ∧ x%2=0 := by omega
    have h8 := BB429RootEven8.rooted_positive_even_eight n x y hn he.1 he.2
    omega
  · omega

/-- Rooted 1(mod32),25(mod32) states cannot be reached. -/
theorem no_1_25 (a b : Nat)
    (hr : Reach a b) (ha : a%32=1) (hb : b%32=25) : False := by
  rcases hr with ⟨n,hn⟩
  by_cases hbig : 13≤a
  · rcases odd_back a b hbig (by omega) ⟨n,hn⟩ with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · exact no_15_26 x y hp (by omega) (by omega)
    · omega
  · have h1 : a=1 := by omega
    subst a
    exact (BB429LowOddMod8.root_ne_one n b) hn

/-- Rooted 1(mod64),23(mod32) states cannot be reached. -/
theorem no_1_23 (a b : Nat)
    (hr : Reach a b) (ha : a%64=1) (hb : b%32=23) : False := by
  rcases hr with ⟨n,hn⟩
  by_cases hbig : 13≤a
  · rcases odd_back a b hbig (by omega) ⟨n,hn⟩ with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · exact no_31_24 x y hp (by omega) (by omega)
    · omega
  · have h1 : a=1 := by omega
    subst a
    exact (BB429LowOddMod8.root_ne_one n b) hn

/-- Rooted 33(mod64),23(mod32) states cannot be reached. -/
theorem no_33_23 (a b : Nat)
    (hr : Reach a b) (ha : a%64=33) (hb : b%32=23) : False := by
  rcases odd_back a b (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · exact no_15_24 x y hp (by omega) (by omega)
  · omega

/-- Rooted 5(mod64),20(mod32) states cannot be reached. -/
theorem no_5_20 (a b : Nat)
    (hr : Reach a b) (ha : a%64=5) (hb : b%32=20) : False := by
  rcases hr with ⟨n,hn⟩
  by_cases hbig : 13≤a
  · rcases odd_back a b hbig (by omega) ⟨n,hn⟩ with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
    · exact no_1_25 x y hp (by omega) (by omega)
    · omega
  · have h5 : a=5 := by omega
    subst a
    exact (BB429LowOddMod8.root_ne_five n b) hn

#print axioms no_15_26
#print axioms no_15_24
#print axioms no_31_24
#print axioms no_1_25
#print axioms no_1_23
#print axioms no_33_23
#print axioms no_5_20

end BB429RootMod64R0
