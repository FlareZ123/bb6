# Candidate m=1, n=8q+1 source reset row

**Status:** the base n=1 q4 prefix already exists in `im-results/agent48-final-rst1/M1OneQ4Prefix.lean`; its 29-step bridge uses the narrower read window [-7,4]. This dossier records the general n=8q+1 lift. `M1OddResidueOneBridge.lean` gives a wider-window [-9,4] finite embedding of the same path, `M1OddResidueOneTargetLeft.lean` formalizes the binary target-left identity, and a deterministic JavaScript replay passes 756 small parameter cases. The arbitrary-width source theorem, suffix/drain composition, original-import compilation, and transitive axiom audit remain open. Keep this in im-results.

## Target source theorem

The next state after Agent 42's m=2 residue-two row is marker 1 with n=8q+1. The intended full counted increment is:

~~~lean
m1OddResidueOne_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+1 < 2^L) (ha : 0<a) :
  run tm2 (proposedIncrementCost 1 (8*q+1) a b)
    (s1Config L (8*q+1) 1 a 0 b h) =
  some (s1Config L (8*q) 0 (a+b+2) 0 (2^b-1)
    (h+5+3*b))
~~~

This is the distinct marker-1 residue-one family. It is not covered by the marker-0 residue-one theorem or the marker-1 residue-three theorem.

## Exact base prefix and finite bridge

For the base L=3,n=1 configuration, the counted left sweep has length 9*a+3 and ends in state 3/head h-(3*a+1). The exact bridge input, relative to that head, is:

[-9,-8,-7,-4,-1,2,3,4]

The same 29-step original-TM2 path is already used by the fixed n=1 q4 prefix. The following wider finite-support embedding is recorded here:

~~~text
state 3, head 0, ones [-9,-8,-7,-4,-1,2,3,4]
  -- 29 steps -->
state 4, head 5, ones [-9,-8,-7,-6,-5,-4,-1,1,2,3,4].
~~~

All pre-final heads lie in [-9,4]. The exactness and head-confinement declarations for this wider embedding are in M1OddResidueOneBridge.lean. The existing M1OneQ4Prefix proof uses only the smaller read window [-7,4], whose start support is [-7,-4,-1,2,3,4]; the extra -9,-8 cells above are not read by the bridge.

After the bridge, a 3*a-step state-4-on-one scan ends at head h+4. Thus the q4 prefix length is 32+12*a.

The q4 cut's left-facing word is:

~~~text
[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1
  ++ binDec (L-3) q ++ lh
~~~

and its right-facing shape is the ordinary q4RightFacing b guard/counter/tail. The base n=1 q4 cut has the same right shape and scan endpoint as the existing m=1,n=3 q4 prefix, with a different low-order left word.

## Arbitrary-width lift and suffix identity

The relevant low-three-bit expansion is:

~~~text
binDec L (8*q+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) q.
~~~

The bridge head window [-9,4], after the counted sweep endpoint, gives the half-line read region x ≥ h-(3*a+10). A general source theorem can therefore be lifted from the base L=3,n=1 prefix using run_frame, provided the left input/cut prefixes and untouched tails are aligned on that half-line. The right tape depends only on b.

The generic q4 suffix starts at state 4/head h with length 39+3*b; the first four moves are already consumed by the q4 prefix ending at head h+4. The remaining suffix is 35+3*b. The target-left identity below is now stated in M1OddResidueOneTargetLeft.lean (source draft, not yet compiled):

~~~text
s1LeftFacing L (8*q) 0 (a+b+2) (2^b-1) =
  d0pow b ++ d1pow 2 ++
    (m1OddResidueOneLeftFacing L q a).drop 1
~~~

where m1OddResidueOneLeftFacing is the q4 cut word above. It follows from:
- binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2);
- binDec L (8*q) = d1 ++ d1 ++ d1 ++ binDec (L-3) q;
- d1pow 2 ++ d1pow a = d1pow (a+2).

Since v2(8*q+1)=0, the reset-prefix cost is 67+12*a+3*b (32+12*a prefix plus 35+3*b remaining suffix). Adding the existing counted drain gives:

~~~text
proposedIncrementCost 1 (8*q+1) a b + 9*b
  = 6*4^b + 42*2^b + 12*a + 19.
~~~

## Finite replay

M1OddResidueOneReplay.mjs reproduces the original TM2 table and S1 encoder and checks:
- exact 29-step bridge endpoint and pre-final head confinement;
- the post-sweep bridge input window for all tested source parameters;
- the q4 prefix endpoint, complete left-facing cut word, right guard/counter shape, and far-tail zeros;
- the exact 35+3*b q4 suffix and 67+12*a+3*b reset-prefix endpoint;
- the target-left identity and counted-cost arithmetic.

The run checked all admissible L=3..8, 0 ≤ q with 8*q+1 < 2^L, 0 ≤ a ≤ 3, and 0 ≤ b ≤ 2: **756/756 cases passed**. This is finite computational evidence only, not the quantified Lean theorem.

## Authentic-root specialization

The current candidate root after middle 22 is m=1,n=16*r-7. Since 16*r-7 = 8*(2*r-1)+1, the new row should instantiate at q=2*r-1. Its candidate endpoint is m=0,n=16*r-8, with:
- A23 = A22+B22+2;
- B23 = 2^B22-1;
- H23 = H22+5+3*B22.

This is a lower-bound itinerary extension only. It does not establish the full TM63 halting run, the exact BB(6) value, or a universal upper bound.
