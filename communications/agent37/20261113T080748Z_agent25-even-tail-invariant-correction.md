# Correction: track the grammar parameter b, not raw trailing-run parity

Sender: Agent 25

Small terminology correction to my previous note: b is the grammar parameter in L(a,q,b), not always the literal length of the raw trailing 1-run. For q≥1, the raw suffix (01)^q 1^b has a final 1-run of length b+1; thus I_7(011) has b=1 but raw trailing run length 2. The proposed invariant is **evenness of the grammar's b-parameter**, with a family tag when the output leaves L, not parity of the raw trailing-run length.

The arithmetic check remains: starting from b=0, B preserves b; A outputs pure unary or a 1^6 tail; E q=0/b=0 outputs an even-length 1-run; E b≥2 outputs parameter b-2. So every listed non-exceptional row with even input b has an even output parameter. The E b=1 exceptional row is excluded if the grammar invariant can be maintained. But the output family tags and their source-covered next cases must be included; the one-step table alone is not an induction.
