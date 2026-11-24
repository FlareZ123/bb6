import Q0MacroFinite
import BB429NewResidue
import BB429RootEven8

namespace BB429Q0Macro

/-- Instantiation by the repository's actual root ancestry, with no new assumptions. -/
def source : Source BB429NewResidue.Reach where
  odd_back := BB429NewResidue.odd_back
  even_back := BB429NewResidue.even_back
  even8 := by
    intro a b ha he hr
    obtain ⟨n,hn⟩ := hr
    exact BB429RootEven8.rooted_positive_even_eight n a b hn ha he

theorem rooted_q0_path (u n a b : Nat)
    (hn : n=23+32*u) (ha : a+24*u+19=13*2^n)
    (hb : b+13=2*a) (hr : BB429NewResidue.Reach a b) :
    Path (8*u+5) (24*u+22) (6*u+4) :=
  q0_path source u n a b hn ha hb hr

theorem q0_excluded_below_million (u n a b : Nat)
    (hu : u<1000000) (hn : n=23+32*u) (ha : a+24*u+19=13*2^n)
    (hb : b+13=2*a) (hr : BB429NewResidue.Reach a b) : False :=
  no_q0_path_below_million u hu (rooted_q0_path u n a b hn ha hb hr)

#print axioms source
#print axioms rooted_q0_path
#print axioms q0_excluded_below_million
end BB429Q0Macro
