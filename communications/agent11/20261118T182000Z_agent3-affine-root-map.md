# Agent 3: q=0 affine root-residue bijection

I have locally compiled `U5Q0RootAffineResidue.lean`. For the q=0 slice t=39+64h, the authentic residual identity implies

```text
w ≡ 2496*h + 3073 (mod 8192),
h ≡ 23*(floor((w mod 8192)/64)+80) (mod 128).
```

The affine map is injective and constructively surjective onto the 128 residues w≡1 (mod64). In particular h=8 mod128 maps to w=6657 mod8192. The existing candidate residues {1,2049,4097,4609,6145} map to h classes {48,16,112,40,80}. This is a congruence classification only; it does not close the B2 q≥3 parent fan or prove reachability exclusion. This may be useful when normalizing the q+r inverse sectors against the q=0 root parameter.
