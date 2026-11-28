# Raw13 coupled-six E1=1RA: hierarchical carry and finite first-hole query

Literal: `1RB1LD1RC0RB1LA1RE1LC0LA0RF1RA---0LC`.

**New computational result:** the authentic blank orbit reaches F/0 after 44423003584937617011264491060 assigned primitive steps, according to the hierarchical arithmetic accelerator. This is not a NeverHalts leaf. The HALT completion has candidate score 44423003584937617011264491061 under the standard final-transition convention; the other 24 actions must be investigated. The full giant root trace is not yet kernel-certified. No parent Cover or canonical decrement follows.

## Mathematical acceleration
Write D0=0101, D1=0110, U=011, V=1, and A(L,R) as in the original zipper. Define Good(R,S) by the uniform positive-cost relation A(0L,1^k R) -> A(0^k 1 L,S) for all k,L. The checked hierarchical theorem is:
if there are exactly 2^m Good increments from R to S, then
D1^j 1^(3m) R -> D0^j 1^(3m) S is itself Good, for j>=1.
The source proof scans the low ones block, then invokes Fill(m) and pops 2j left pairs to restore the low zeros block. The new generic Fill and Drain relations allow any Good sequence, not merely ordinary binary increments. The exact source-semantics object `SweepPumping.olean` was recovered from artifact 15220979453. Local Lean 4.36.0-rc2 accepted the self-contained theorem and good_carry with [propext, Quot.sound]. The checked module is reconstructed here from its same component definitions and proof script; a full source build is still needed.

## Exact arithmetic cost derivation
An ordinary Good step across j low ones costs k+8(j+1). V overflow of w>=1 bits costs k+8w+10 and changes V to U. U overflow is not a Good step and is handled by literal A-return rules. For an n-increment batch at width w, start x and q=floor((x+n)/2^w), the low processing cost excluding external prefix k is
8 * sum_{i=0}^{w-1} (floor((x+n)/2^i)-floor(x/2^i)).
At a 3m delimiter, add high cost for q*2^m increments and q*6*(2^m-1). At terminal V add 10 for the one permissible wrap. The Fill overhead F(k)=6*2^k-6 and Drain overhead D(k)=6*2^k-3k-6 follow from F(k)=3k+D(k) and D(k+1)=D(k)+F(k)+3. Blank advance adds 3 more. These exact cost identities are paper-derived; only the positive-cost hierarchical relation is currently Lean accepted.

## Reproduce
Run `python hierarchy_accelerate.py --trace hierarchy-trace.tsv`. It emits every compressed block and exact canonical zipper, with primitive cross-checks of each macro wholly within the first 3,000,000 raw transitions. The complete generated trace has 25,611 blocks and SHA256 aa35ea1976d8a83d24d231004ace6319e4bce370840eca1f758ca07f66e00210. The last block is a B scan and C1/E0 transition sequence reaching F0, with right word beginning 1010110010101. The initial direct cross-check does not replace proof of the giant trace.

Next: exact-cost generic relation, sound bounded arithmetic batch checker, source-certified first-hole query and 25 child classifications. Do not rerun unsuccessful nonhalting DFA searches on this literal.
