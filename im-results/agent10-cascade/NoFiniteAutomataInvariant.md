# No ultimately periodic reset-height safety invariant for #746

## Theorem

Let S be any forward-closed safe set of physical configurations of the exact six-state machine #746 containing the blank configuration. The set of heights h for which S contains the reset configuration

    0^∞ E> (10)^h 1 0^∞

cannot be ultimately periodic, or even contain an infinite arithmetic progression. In particular, no regular configuration-language inductive safety certificate exists for this machine, of either tape orientation or any finite automaton size.

This is an impossibility result about a proof system, not a proof of nonhalting.

## Arithmetic lemma

For every a,b in N, c in Z, positive modulus m, residue r in Z, and threshold N, there exists n>=N with

    a*b^n - n - c = r (mod m).

Proof by strong induction on m. Modulus 1 is immediate. For m>1 the modular power sequence a*b^n has a repetition at indices i,i+t with 0<t<m: if a zero occurs it repeats at the next index, otherwise there are only m-1 nonzero states. This repeat persists at every index >=i and for every multiple of t. Put d=gcd(m,t)<m. The induction hypothesis supplies k>=max(i,N) with d dividing a*b^k-k-c-r. By Bezout there exists j>=0 with t*j congruent to a*b^k-k-c-r modulo m. The index n=k+t*j then gives the required congruence.

In particular F(n)=4*2^n-n-4 is nonnegative and unbounded, and meets every residue class modulo every positive modulus arbitrarily far out. Any infinite arithmetic progression of natural heights therefore contains a fatal height F(n).

The full arithmetic lemma, conversion to natural fatal heights, finite-state repetition, and generic strict-growth inductive obstruction are kernel checked in [FatalResidues.lean](FatalResidues.lean), Lean 4.36.0-rc2. Axioms are only propext, Classical.choice, Quot.sound.

## Source connection

The pinned Cryptids file [M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean) defines highLevelEncode (.C h 0) as exactly the physical configuration above. Its universal is_valid_highLevel_acceleration supplies genuine positive-time transitions or a genuine halt for all prepared states. The authentic blank orbit reaches .C 2 0. Existing exact local bridges: [OriginalNextBridge.lean](OriginalNextBridge.lean), [ExactGate.lean](ExactGate.lean) (fatal_path, for every natural n), [FirstOutcome.lean](FirstOutcome.lean) (first_outcome_exists), [FirstInverseComplete.lean](FirstInverseComplete.lean) (reset_parent_iff), [ResetParentStrict.lean](ResetParentStrict.lean) (strict height growth).

Hence a safe closed S must contain the root reset, cannot contain any F(n), and must contain a strictly increasing sequence of reset heights: apply total first-outcome existence repeatedly, eliminating halt by safety. Any regular language restricted to the fixed unary-block family is ultimately periodic in h, since reading (10) repeatedly iterates a single finite-state map. This holds in either orientation, including the DFA/NFA Boolean-vector semantics of FAR. An infinite ultimately periodic set contains an infinite progression, contradiction.

More generally any semilinear height separator is impossible. A context-free configuration language also fails: take its inverse image under a fixed repeated-block encoding, removing the fixed prefix and suffix by quotient. The resulting unary context-free language is regular (Parikh's theorem). 

## Weighted FAR scope

For a deterministic finite-state scan with additive integer weights, reading the fixed block repeatedly eventually follows a finite state cycle. On each residue phase of that cycle the accumulated weight is affine in the number of periods. Membership in any fixed finite union of integer intervals is eventually constant per phase. Fixed congruence conditions give a further finite period. The same argument extends to finite-dimensional additive weight vectors with Presburger acceptance (affine substitution leaves a unary Presburger predicate).

Consequently ordinary additive-weight FAR with fixed interval tests, including a two-sided scan where the other side of the reset is fixed, cannot provide a valid safe invariant for #746 either. This does not cover nonlinear arithmetic weights, arbitrary matrix products, nonregular exponent-sensitive certificates, or arbitrary proof methods.

## Verification boundary

The general arithmetic and finite-state obstruction is fully checked in Lean. The application to raw physical automata and weighted scans above is a paper argument using the existing source-certified reset semantics, not yet one end-to-end Lean theorem. Do not interpret this as a resolved holdout, a new lower bound, or an exhaustive upper-bound result. It eliminates an entire family of prospective deciders even if the machine ultimately halts.
