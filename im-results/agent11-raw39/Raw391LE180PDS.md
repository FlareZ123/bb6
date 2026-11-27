# Exact one-stack abstraction for Raw39 1LE180

This is an intermediate reduction, not a closure of leaf 180. The literal
A-return rules are in [Raw391LE180Sections.md](Raw391LE180Sections.md).
The aim is to replace simultaneous guessing of two tape DFAs with finite
pushdown saturation on the exact other tape.

Let L be any deterministic finite abstraction of the physical left word
(read far to near), with the blank state fixed under 0. Retain the right
word exactly, read head first. Controls are A(l) and E(l), plus prefix
trie controls. For an A0 rule u -> v with cut h, replace stack prefix u
by v[h:] and change l to L(l,v[:h]). For A1, enter E(l) without changing
the right stack, then for each predecessor l' with L(l',1)=l pop an
abstract left 1 and prepend 0 to the exact stack; for every a and l0
with L(l0,a0)=l exit to A(l0), prepending a0. Thus every concrete A1
return (left suffix a01^j) is simulated, without any bound on j. Abstract
paths can be spurious. Finite padded tape words suffice for every finite
true counterexample: choose initial zero padding exceeding its excursion.

The target NFA accepts right prefix 011 from every A(l). For each
pushdown rule (p,b)->(q,w), add p -b-> s whenever q -w-> s exists.
An induction on abstract path length proves the saturated NFA contains
all predecessors of the target. If the initial control has no accepting
path labeled only zeroes, this proves concrete nonhalting. The finite
edge table is a certificate; minimality or faithfulness of abstraction
is not needed for soundness. The symmetric construction retains the left
stack exactly and abstracts right.

## A true phase-sensitive left language invariant

Ignore leading zeros in the physical left word. All nonfinal one-runs
have length >=2 and all zero runs have length <=3. A final isolated 1
may have at most one following zero. At A0 every one-run has length >=2.
The seven-state partial DFA (states 0..6; -1 forbidden) has transitions
on 0,1:
0:(0,1), 1:(3,2), 2:(4,2), 3:(-1,-1), 4:(5,1), 5:(6,1), 6:(-1,1).
A0 allowed states 0,2,4,5,6; A1 any of the seven.

Proof: the A0 full pushes append 1100, 11000, or 11100; bounce
pushes append 10 or 110 and leave scanned 1. Starting with the A0
condition, these preserve the claimed grammar (a final existing run may
merge with the new run). A1 removes a suffix a01^j and scans a.
Every prefix retains the base grammar. If a=0 and j>0, the removed run
was preceded by at least two zeros (or left blank), hence no final
isolated one remains. If a=0 and j=0, the removed suffix 00 cannot
follow a singleton, by its one-zero limit. Consequently A0 retains the
stronger condition. Blank starts in state 0. This proof is on paper,
not Lean-accepted, and does not exclude the bad right prefix.

[raw391le180_pds.py](raw391le180_pds.py) implements the guarded
left abstraction, exact right stack, and saturation. The partial
left grammar is optional, and the included product tracks a suffix.
No successful unbounded safety certificate was found. Tested ordinary
left suffix lengths through 11, right suffix through 9, and guarded
left suffix through 10. Counterexample-guided Aho-Corasick suffix
refinement, using the lifetime of the first mismatched abstract pop,
continued to generate spurious paths (left over 2400 states, right over
5000). These are negative search results, not lower bounds on possible
pushdown certificates. Larger two-tape SAT synthesis was inconclusive.
A better abstraction must track longer-range correlations, not simply
increase a fixed window. No source acceptance, no residual decrement.
