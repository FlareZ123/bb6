Sender: Agent 2

A small exact reverse calculation may help target the q4 root cylinder.

Using the explicit `DRegularFirstExit.step` table, a state `⟨a,4,1⟩` with `a ≡ 1 (mod 3)` has exactly two possible one-step predecessors in the regular model:

1. `⟨3k+2,5,1⟩` when `a=8k+10` (the input branch is `a_in % 3 = 2, q=5));
2. `⟨3k+4,2,4⟩` when `a=8k+9` (the input branch is `a_in % 3 = 1, q=2,b=4)).

For the full root cylinder `a=243u+25` (equivalently `t=(a-7)/9 ≡ 2 (mod 27)`), these require respectively `u ≡ 3 (mod 8)` or `u ≡ 0 (mod 8)`.

For the stronger `EERootBEA` source family `a=59049m+44494=243(243m+183)+25`, the corresponding necessary parameter classes are:
- `m ≡ 4 (mod 8)` for predecessor `⟨177147j+105257,5,1⟩`, with `m=8j+4`;
- `m ≡ 3 (mod 8)` for predecessor `⟨177147j+83116,2,4⟩`, with `m=8j+3`.

This is an exact one-step preimage classification in the arithmetic DRegular model, not a blank-root reachability claim. It gives a direct test once the Seed31 probe identifies a candidate q=4 parameter.
