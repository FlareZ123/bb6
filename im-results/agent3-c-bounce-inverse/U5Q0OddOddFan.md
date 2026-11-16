# U5 q=0 odd/odd terminal: complete source-parent fan (algebraic draft)

Status: **intermediate derivation, not yet Lean-formalized or source-certified**. This note records a reusable exact inverse classification for the residual q=0 target; it is not a blank-unreachability proof.

## Target and existing pullback

For the M=8w residual, the q=0 member of the terminal y=3 parent fan is
[
P=(8p-3,4p-1),qquad p=m+1=8t+1,
]
so
[
P=(64t+5,32t+3).
]
The existing exact odd/odd valuation-three and even/odd-four inverse equivalences pull this target back to
[
X_t=(44t-1,42t-1).
]
For w odd, the congruence t+w=0 (mod 8) leaves t=1,3,7 (mod 8), corresponding respectively to w=7,5,1 (mod 8).

## Exact source-parent classification

Let t be odd and positive. Put x=44t-1, y=42t-1. Then
[
x+y=2(43t-1),qquad x+y+1=86t-1	ext{ is odd},qquad x+2y=128t-3.
]

Applying the complete original-source grammar `section_preimage_all_iff` to `secNext (a,k)=some (x,y)` gives the following necessary classification:

[
exists q,U:quad
43t-1=4^qU,quad Uge4,quad Uequiv0pmod2,
]
[
a=U-2,qquad 2k+U+6q=128t-8,qquad 0<k,quad a<2k.
]

Here q is the even-bounce depth parameter n/2. Conversely, any q,U satisfying these equations and source side conditions gives the corresponding even-a bounce branch of `section_preimage_all_iff`, so this is the exact surviving parent fan once the exceptional a=0 branch is ruled out.

### Why all other source branches disappear

- The direct branch has y=2k+2, impossible because y is odd.
- The k=0 branch has y=2, also impossible.
- For a=1, the only branch compatible with y≥5 requires x+y+1=2^n·16, impossible because x+y+1 is odd.
- For odd a≥3, the high branch requires x+y+1=2^n(2(a-1)+8), again impossible by parity.
- For a=0 and k≥2, the grammar gives
  [
  x+y=2^ncdot8,qquad 2k+9+3n=x+2y.
  ]
  The cost equation forces n even, say n=2r. The sum equation then gives
  [
  43t-1=2^{n+2}=4^{r+1}.
  ]
  Reducing modulo 43 yields (4^{r+1}equiv-1pmod{43}), but (4^7equiv1pmod{43}). Raising the former congruence to the seventh power gives (1equiv-1pmod{43}), contradiction. The exceptional a=0,k=0 and k=1 cases are already impossible from the grammar.

### Derivation of the surviving fan

For even a≥2 and k>0 with 2k>a, the only remaining branch is
[
x+y=2^n(2(a-1)+6)=2^{n+1}(a+2),
]
[
(2k-a+3)+(2(a-1)+6)+3n=x+2y.
]
Since x+2y is odd and a is even, the second equation forces n even. Write n=2q and U=a+2. Dividing the first equation by 2 gives (43t-1=4^qU); U is even and at least 4. Substituting a=U-2 and n=2q into the cost equation gives (2k+U+6q=128t-8).

For t≡1,5,7 (mod 8), v2(43t-1) is respectively 1,1,2, so only q=0 is possible and the unique parent is the familiar low-valuation parent ((43t-3,(85t-7)/2)). For t≡3 (mod 8), write t=3+8u; then v2(43t-1)=3+v2(16+43u), which is at least 3 and can be larger for suitable u. The admissible q values satisfy 2q+1≤v2(43t-1), with the additional endpoint condition U≥4 excluding any q for which U=2. Thus the w≡5 (mod 8) residual is a genuine parameter-dependent multi-depth parent fan, not merely another application of the unique low-valuation parent. This explains why the w≡5 (mod 8) residual is a genuine multi-depth parent fan, not merely another application of the unique low-valuation parent.

## Next mathematical task

For t≡3 (mod 8), eliminate every admissible parent in the finite-but-parameter-dependent fan above, or prove a reusable invariant that excludes the whole fan. For t≡1,7 (mod 8), continue the unique parent through the appropriate even/odd or even/even source normalization. Do not infer blank-unreachability from the parent classification alone.
