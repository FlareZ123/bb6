# F119: two-tag ternary acceleration and terminal exponent restriction

Machine: `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` (upstream #417 / suspect_15). This is a live member of the historical 608 holdout roster.

## Established theorem

For the copied upstream three-counter recurrence, blank-root halting is equivalent to reaching a section `(3^k,1)` with `k mod 12 = 0 or 3`. The immediately preceding section, whenever such a power is reached from a nonterminal root path, must have tag 1 and ternary valuation 1; its first coordinate is (9·3^k−33)/10 when k mod 4 = 3 and (9·3^k−39)/10 when k mod 4 = 0.

This eliminates all other terminal exponent classes. Neither surviving class has yet been proved unreachable, so this is not a nonhalting certificate.

## Reduction

A section (x,c) denotes D(0,x−1,c), x≥4, c∈{1,2}; the initial section is (4,1). Factor x=3^h m with 3∤m. The following returns are exact:

* m=3t+1, t≥1: (x+c+h+t+2,1).
* m=3t+2: (x+c+h+t+3,1).
* m=1: let r=(c+x−1+h) mod 3. If r=0 the recurrence halts; otherwise the return is (x+c+h+4−2r,r).

Every nonterminal return increases x strictly. In the root-compatible section invariant, tag 2 occurs only at x=3^a+a+1, a≥2. Such a section and its generic successor lie strictly between consecutive powers. Power-to-power returns are also impossible.

For a generic tag-1 predecessor of 3^k, put p=3^h and M=3p+1. Powers of three modulo M are among ±3^j, 0≤j≤h. For h≥2 the necessary residue is p+h+3 or 2p+h+4, both excluded by the gaps between these signed powers. For h=0 the output is even. For h=1 the residue calculation modulo 10 gives the two formulas above. The halt test imposes k mod 3=0.

## Evidence and reproduction

`F119.lean` is a pure Std proof, checked locally with Lean 4.36.0-rc2. Run `lean F119.lean`. Main declarations: `F119.root_halts_iff`, `F119.incoming_power`, `F119.root_halts_iff_restricted_power`. The printed axiom sets are subsets of propext, Classical.choice and Quot.sound; no sorry or native_decide.

The proof currently uses a literal transcription of the arithmetic transition from Google DeepMind cryptids, Apache-2.0, commit 3647718b5df22e1a61462dec0376bd204526285a, [original module](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean). That module supplies the raw-machine acceleration theorem. Import-connected equivalence remains to be checked; this local result alone is not a source-connected raw-machine theorem.

## Next obligation

Decide reachability from (4,1) of the two remaining power classes. A useful inverse formulation for tag-1 generic sources is y=(3p+1)t+pr+h+3+δ, where r∈{1,2}, p=3^h, δ=1 exactly for r=2. The inverse is finite for a given target, but a uniform proof over unbounded exponents needs stronger arithmetic structure.
