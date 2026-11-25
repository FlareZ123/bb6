# From finite block-FAR invariants to primitive MITM invariants

This is a mathematical conversion argument and an independently checked computational application. The conversion is not yet formalized as a general Coq/Lean theorem; individual converted witnesses are checked by the original BusyCoq MITMDFA decider.

## Proposition (finite-width lifting)

Consider a two-symbol deterministic partial Turing machine with blank 0. Fix a block width w ≥ 1. Suppose:

1. A finite left DFA summarizes full blocks from the distant end toward the head. It starts at state l0 and l0 --0^w--> l0. Missing transitions can be totalized by a dead state.
2. A finite right NFA reads blocks nearest to farthest, starting from a state determined by the left DFA state, control state, and block-entry direction. A set Z of terminal states accepts a blank right ray. Its reverse preimage under the zero block is Z. (For an existing certificate with forward blank extension, use the backward-zero closure of its accepting set, interpreting acceptance as existence of a finitely zero-padded representation.)
3. The accepted block-entry configurations include the blank initial configuration. Each accepted block entry has a defined strictly positive finite primitive execution within that block, terminating at the next block entry, which is accepted.

Then there are two finite binary DFAs with zero self-loops at their initial states such that a finite closed relation on their state pairs, the current primitive state, and the scanned bit contains the blank initial tuple and contains no undefined transition. This is a primitive two-sided DFA nonhalting certificate.

### Construction

Reverse-determinize the right NFA: its state is a subset S of NFA nodes, initialized to Z. Reading a block a from far to near changes S to pre_a(S), the set of nodes having an a-edge into S. Thus, after reading all full right-tail blocks far-to-near, membership of a control node in the resulting subset is precisely acceptance of the corresponding right-tail language. The zero-block transition fixes Z.

For either block DFA, read an ordinary finite bit stack from far to near. Keep w components indexed by p=0,...,w-1. Component p holds the full-block DFA state and a pending word of p bits. It represents the decomposition obtained by padding the distant end with zeros until the number of ungrouped near-end bits is p. The padding is unambiguous modulo w, and adding any further full zero blocks has no effect. The initial vector has the initial full-block state and p pending zero bits for each p.

Appending a bit advances every component: p<w-1 goes to p+1 with that bit appended; p=w-1 consumes the resulting full block and goes to component 0. For the right stack, encode the consumed block in reverse bit order relative to the far-to-near read. This is a deterministic finite transition, and appending 0 to the blank vector leaves it unchanged.

Let D be the number of original left states including any totalizing sink, and N the number of right NFA nodes. The product bounds on the left/right phase DFA state counts are respectively D^w · 2^{w(w-1)/2} and 2^{Nw+w(w-1)/2}. Only states reachable by finite pushes need to be interned.

### Proof of closure

Let E be the union, over all relative block alignments, of the accepted concrete block-entry configurations. Let I consist of E and all intermediate primitive configurations along the stipulated finite executions from E to the next entry. Assumption 3 implies I contains the blank start and every configuration in I has a defined primitive successor in I.

Membership in I is saturated under equality of the two phase-DFA states, the current machine state, and scanned bit:

- For each possible head offset p within a block, the left component p and right component w-1-p give the outside full-block summaries. They also give the exact p left bits and w-1-p right bits of the current block. Together with the scanned bit, these reconstruct the entire current block.
- There are finitely many possible entry states, entry directions, and entry block contents. For any such choice, acceptance of the entry configuration depends only on the two outside full-block summaries and the entry block. Indeed, the right subset determines whether the appropriate control node accepts the entry block followed by the right tail.
- While the primitive head stays inside this block, both outside full-block rays are unchanged. Whether the selected entry has a finite internal prefix to the current state, offset, and block is a finite local question. Therefore the existence of such a prefix is determined by exactly the phase-DFA tuple.

Let R contain the abstract tuples represented by I. Every reachable DFA state has a concrete finite-stack representative. For an arbitrary abstract right move from (q,l,b,r) in R, choose any right predecessor r' and bit c with δ_R(r',c)=r. Choose a finite stack representing r', append c, and independently choose a left stack representing l. By saturation, that concrete configuration lies in I. Its primitive successor lies in I and represents exactly (q',δ_L(l,write),c,r'). Hence all right-pop predecessor edges are safe. The left-move argument is symmetric. The zero self-loop covers implicit blank padding. Thus R is closed under every abstract primitive push/pop move. No tuple in R has an undefined transition, and the blank tuple belongs to R.

This argument does not depend on how the block certificate was synthesized. A finite primitive closure search from the blank tuple therefore succeeds with the lifted DFAs whenever the hypotheses hold (subject to resource bounds). Restricting to discovered push edges, as in the original CTL algorithm, can only reduce the required abstract relation.

## Application

`block_phase_dfa.py` implements the construction using the exact arrays from Agent13's existing block-FAR generator. All eight block-FAR held q0 tables passed full primitive inverse-edge closure locally. The q3500 table instead has a compact direct primitive run-residue witness (four nearest runs, length modulo 9). The original BusyCoq source verification runs are 45607275287 and 45607737965; exact checkpoint consumption is handled separately by Agent5RosterComplement.v and prepare-phase-consumption.py.

Scope: this conversion supplies source-language certificates for nonhalting cylinders. It does not by itself establish that the original source search is globally covered, nor an upper bound on BB(6).
