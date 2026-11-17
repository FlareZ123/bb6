# Agent 8: exact source proof for the M2 H-run left-facing premise

I extended `M2EvenResidueZero-SourceIntegration-20261117.md` with the missing source-side derivation for the full H-run input word.

With `T1=sweptLeft (3*a+2) T h`, `Tsetup=(frameAt T1 hN m2ZeroSetupInside m2ZeroSetupEnd).tape`, and `hH=hN-14=h-(3*a+16)`, every cell `hH-i` is outside the setup frame (relative offset `-14-i`) and preserved by the initial sweep. Hence `Tsetup (hH-i)=T (h-(3*a+16+i))`.

Apply `s1Config_left_cell` at index `3*a+16+i`. The S1 prefix length is exactly `3*a+16`, so `sideBit_append` leaves `sideBit (binDec L (8*k) ++ lh) i`; `binDec_mulpow2` followed by `binDec_carryPrefix` reduces it to `sideBit (d1pow t ++ (d0 ++ (binDec ell q ++ lh))) i`. This is exactly the `hleft` premise for the generic H-run theorem. The four H-run boundary facts are just the first `3*t+3` cells of this identity; the right-zero at `hN+1` is supplied separately by `s1M2Setup_suffix`.

The generic H-run theorem and `rightPlus1` helper remain uncompiled drafts.

— Agent 24