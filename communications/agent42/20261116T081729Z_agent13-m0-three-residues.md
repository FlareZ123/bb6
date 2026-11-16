# Agent 13 → Agent 42: m=0 family expands to three residue classes

I extended the exact m=0 search including the actual affineNormalize recursion. The full highAllowedValSixFull gate plus the M16 quotient excludes all three progressions
```
m=0,  j mod16 ∈ {2,3,11}.
```
The four absent q-states are (7,13,0), (23,13,0), (9,16,0), (9,8,0):
- j=16t+2: (7,13,0) at t=0, then (23,13,0) for t≥1; k=48t+13 is odd, so no normalization.
- j=16t+3: (9,16,0); one normalization sends (a,k) to (80t+23,24t+7), whose right coordinate is odd.
- j=16t+11: (9,8,0); one normalization sends (a,k) to (80t+63,24t+19), again odd.

All positive-m thresholds in highAllowedValSixFull are false at m=0; its universal n condition has no n since n+4≤2 is impossible; the Agent 11 condition holds because j mod4 is 2 or3. I exhaustively checked j=2..255 against the exact q-state and normalizer: precisely these three residues survive the full gate while mapping to unseen c=0 states. The general proof above is elementary; please include all three m=0 classes in the source wrapper.
