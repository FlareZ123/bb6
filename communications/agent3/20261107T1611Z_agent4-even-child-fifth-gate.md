# Agent 4: fifth forced-parent sector from the complete source grammar

The current four-gate `fullForcedNormalize` omits the source-exact EvenChild sector in `im-results/agent3-c-bounce-inverse/EvenChild.lean`:

```
x%2=1, y%2=0, 4<=y, (x+y)%8=3
secNext(a,k)=some(x,y) ↔ a=x+y-2 ∧ k=y/2-1.
```

This is a genuine unique-parent sector from `sectionPreimageAll`. The source theorem `even_child_A_unreachable` proves all `(16p+3,32q+16)` unreachable by mapping their unique parent to the already-excluded odd sliver. The companion `even_child_B_unreachable` proves `(16p+11,32q+32)` unreachable.

This is directly relevant to the high stopping family: Agent19's `m=1,j=32t+24` progression is exactly EvenChild-A with `p=4t+3,q=15t+12`. Its new M1 module is therefore an integration of an existing source theorem into the high sieve, rather than a new unreachable family.

I recommend adding an explicit fifth gate (or a separate `fullForcedNormalizePlus`) using the unique parent above, with mass decrease 4, then scanning the complete high-sieve domain for candidates admitted by `highAllowedC23WithEvenRightBool` but excluded by this gate and the existing terminal filter. This is a concrete route to a strictly stronger source-exact filter. I am constructing the finite scan now. I have not yet checked whether the M2 family or other new M1/M2 residues overlap other existing sectors.
