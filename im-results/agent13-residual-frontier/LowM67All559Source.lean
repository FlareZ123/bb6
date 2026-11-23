import LowM67All523Source
import LowM67FiveD23Source

namespace BB6.Agent13Low559Source

/-- Finite union of disjoint all-time nonreachability cylinders for the
    original Machine C blank section. In the common z-modulus 4096,
    the original 16/128 plus the original three-parent 1/512, our
    additional two three-parent classes, and five new two-parent classes
    total 512+8+2+1+16+8+4+4+4 = 559 forbidden classes.
    No result about other m-families or the Machine C high branch follows. -/
theorem low_stop_fivehundredfiftynine_mod4096_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : ((((z%16=13 ∨ z%64=5 ∨ z%32=25 ∨
              z%128=9 ∨ z%128=21) ∨ z%512=65) ∨
            z%2048=1729 ∨ z%4096=3521) ∨
          (z%256=165 ∨ z%512=105 ∨ z%1024=469 ∨
           z%1024=869 ∨ z%1024=585)))
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  rcases hz with h523|hfive
  · exact BB6.Agent13Low523Source.low_stop_fivehundredtwentythree_mod4096_unreachable
      z m k hm h523 hstop
  · rcases hfive with h165|h105|h469|h869|h585
    · exact BB6.Agent13FiveD23.low_stop_m67_z165_mod256_unreachable
        z m k hm h165 hstop
    · exact BB6.Agent13FiveD23.low_stop_m67_z105_mod512_unreachable
        z m k hm h105 hstop
    · exact BB6.Agent13FiveD23.low_stop_m67_z469_mod1024_unreachable
        z m k hm h469 hstop
    · exact BB6.Agent13FiveD23.low_stop_m67_z869_mod1024_unreachable
        z m k hm h869 hstop
    · exact BB6.Agent13FiveD23.low_stop_m67_z585_mod1024_unreachable
        z m k hm h585 hstop

#print axioms low_stop_fivehundredfiftynine_mod4096_unreachable
end BB6.Agent13Low559Source
