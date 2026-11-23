import BB429CenterLine
import BB429RootOddRowsStrong
import Lean.Elab.Tactic.Omega

/-!
# Root-center boundary: two additional forbidden 2-adic cylinders

We refine the all-time u mod32 center-line restriction by three exact
inverse steps, excluding center first-counter classes 25 and 49 mod64.
No assumption that any survivor is reachable.
-/

namespace BB429CenterLineMod64

open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- An authentic positive source first counter 1(mod8) cannot have
    a 5(mod8) second counter, by the strengthened 1(mod16) row
    and the genuine two-step 9(mod16) row. -/
private theorem no_root_one_five (a b : Nat)
    (hr : Reach a b) (ha : 33 ≤ a)
    (ha8 : a%8=1) (hb8 : b%8=5) : False := by
  by_cases h1 : a%16=1
  · obtain ⟨n,hn⟩ := hr
    have hh := BB429SevenStrong.rooted_one_strong n a b hn h1
    omega
  · have h9 : a%16=9 := by omega
    exact BB429RootOddRowsStrong.rooted_not_9_5
      a b hr ha h9 hb8

/-- A convenient direct obstruction for the only other first
    inverse branch: 3(mod8),3(mod8) genuine root visits. -/
private theorem no_root_three_three (a b : Nat)
    (hr : Reach a b) (ha : 13 ≤ a)
    (ha8 : a%8=3) (hb8 : b%8=3) : False := by
  rcases odd_back a b ha (by omega) hr with
    ⟨p,q,hp,hpa,hqb⟩ | ⟨p,q,hp,hpa,hqb,hb4⟩
  · obtain ⟨n,hn⟩ := hp
    have hh := BB429RootEven8.rooted_positive_even_eight
      n p q hn (by omega) (by omega)
    omega
  · omega

/-- The entire u=25(mod64) center reset line is unreachable
    from the actual blank return orbit above the small-value cutoff. -/
theorem rooted_center_not_25_mod64 (u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u)
    (hu25 : u%64=25) : False := by
  rcases odd_back u (2*u) (by omega) (by omega) hr with
    ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
  · exact no_root_three_three p q hp (by omega) (by omega) (by omega)
  · rcases odd_back p q (by omega) (by omega) hp with
      ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
    · obtain ⟨a,b,hab,hra,hbs,hmod⟩ :=
        even_back r s (by omega) (by omega) hrs
      exact no_root_one_five a b hab
        (by omega) (by omega) (by omega)
    · omega

/-- The u=49(mod64) center reset line is likewise unreachable,
    but the forced first inverse branch is the F rather than S one. -/
theorem rooted_center_not_49_mod64 (u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u)
    (hu49 : u%64=49) : False := by
  rcases odd_back u (2*u) (by omega) (by omega) hr with
    ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
  · rcases odd_back p q (by omega) (by omega) hp with
      ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
    · obtain ⟨a,b,hab,hra,hbs,hmod⟩ :=
        even_back r s (by omega) (by omega) hrs
      exact no_root_one_five a b hab
        (by omega) (by omega) (by omega)
    · omega
  · exact no_root_three_three p q hp (by omega) (by omega) (by omega)

/-- Six necessary 2-adic cylinders for any true blank-root visit to
    the center boundary (u,2u), u>=129. -/
theorem rooted_center_mod64 (u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u) :
    u%64=13 ∨ u%64=17 ∨ u%64=29 ∨
    u%64=45 ∨ u%64=57 ∨ u%64=61 := by
  have h32 := BB429CenterLine.rooted_center_mod32 u hr hu
  have h25 : u%64≠25 := by
    intro h
    exact rooted_center_not_25_mod64 u hr hu h
  have h49 : u%64≠49 := by
    intro h
    exact rooted_center_not_49_mod64 u hr hu h
  omega

#print axioms no_root_one_five
#print axioms rooted_center_not_25_mod64
#print axioms rooted_center_not_49_mod64
#print axioms rooted_center_mod64

end BB429CenterLineMod64
