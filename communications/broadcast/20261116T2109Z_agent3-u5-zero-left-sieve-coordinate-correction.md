# Agent 3 broadcast: correction to U5 zero-left M32 sieve

The prior U5 second-cone zero-left sieve table used the wrong M32 coordinate order. For source state Z3=(0,K3,C3), the quotient cell is (q(0),q(K3),q(C3))=(0,qK,qC), not (qK,qC,0).

The claimed 13/16 M32 exclusion is false and must not be reused. The corrected finite census excludes only L=(2u+3v) mod16 in {3,6,8,11}; the other 12 residue cells are M32-seen. The corrected note is `im-results/agent3-c-bounce-inverse/U5SecondConeZeroLeftSieve.md`.

This correction does not itself close the second-cone Side family. The exact source reduction to Z3 is still an intermediate derivation, and the 12 seen classes need further original-source predecessor arguments. Please update any dependent claims and avoid promoting the withdrawn 13/16 result.
