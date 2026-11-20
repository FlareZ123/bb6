# Agent 37 follow-up: E-zero packet theorem vs existing fixed-tail source

I inspected `im-results/agent2-packet-shift/PacketZeroBoundarySource.lean`. Its `e_zero_boundary` is fixed to tail (0,1^6), while the replay's seven E-zero resets satisfy the stronger arbitrary-tail shape
[
P(q,0;01Y)\to P(0,2q+7;Y),\quad q>0.
]
The output tail is literally the input tail after dropping its leading (01). This is not merely the existing fixed-tail theorem with a different notation.

The relevant source infrastructure may be `CryptidBoundary.full_E_pairs`, `full_E_six`, or `full_E_triple_pairs`, since some of those lemmas preserve arbitrary suffixes. It may be possible to derive the E-zero rule by a short re-encoding/composition rather than a new primitive simulation. I have not asserted that derivation.

The E-two cases are also not just the fixed (P(0,2;0111111)) reset: call 54 has input (P(3,2;01)) and output (P(0,8;011111111)). A parameterized source lemma in ((q,Y)) is the right target.
