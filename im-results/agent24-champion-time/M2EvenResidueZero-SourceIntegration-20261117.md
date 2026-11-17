# M2, n=8k: source-side H-run to q4 cut (proof derivation)

**Status:** derived integration plan, not a compiled source theorem. It closes the word-level gap between the existing M2 residue-zero setup/H-run/postlude frames and the generic q4 suffix interface.

## 1. Exact factorization and quotient stream

Assume `k>0`, `8*k<2^L`, and `a>0`. From `L>=4`, obtain `k<2^(L-3)`. Apply `exists_odd_factor_bounded (L-3) k`:

~~~lean
k = (2*q+1)*2^t
L = ell+4+t
q < 2^ell
~~~

The existing S1 encoder identities give:

~~~lean
binDec L (8*k) = d1pow 3 ++ binDec (L-3) k
binDec (L-3) k = d1pow t ++ d0 ++ binDec ell q
binDec L (8*k-1) = d0pow (t+3) ++ d1 ++ binDec ell q
~~~

The first equality is `binDec_mulpow2`; the second is `binDec_carryPrefix`; the third is `binDec_sub_one_carryPrefix` at valuation `t+3`.

In `s1LeftFacing L (8*k) 2 a 0`, the prefix before `binDec (L-3) k` has length `3*a + 4 + 3 + 9 = 3*a+16`:

~~~lean
d1pow a ++ markerWord 2 ++ d0 ++ d1pow 3
~~~

The setup window is the 14 cells at indices `3*a+2 .. 3*a+15`, exactly `[false,true] ++ d0 ++ d1pow 3` (already proved by `s1M2Setup_suffix`). Therefore the first quotient bit is precisely at `hH=hN-14`, where `hN=h-(3*a+2)`. After setup, the H-run's left-facing input is `d1pow t ++ d0 ++ tail`, where `tail=binDec ell q ++ lh`.

## 2. H-run premises and output word

Let `Tsetup` be the setup output tape and `hH=hN-14`. The H-run facts follow directly from the quotient stream and the setup frame:

- `leftOnes Tsetup hH (3*t)` from `d1pow t`;
- `Tsetup (hH-3*t)=false` and `Tsetup (hH-3*t-1)=false` from the first two bits of `d0`;
- `Tsetup (hH-3*t-2)=true` from the third bit of `d0`;
- `Tsetup (hN+1)=false` from the setup output window at relative `-13`.

The existing `m2ZeroSetup_HRun_Postlude` needs only the first, two zero boundaries, and right-zero boundary for the run itself; the third bit is needed for the exact output-word lemma.

More generally, the full H-run input word follows from the same source calculation. Put `T1=sweptLeft (3*a+2) T h`, `Tsetup=(frameAt T1 hN m2ZeroSetupInside m2ZeroSetupEnd).tape`, and `hH=hN-14=h-(3*a+16)`. For every i, the cell `hH-i` is outside the setup frame (its relative offset is `-14-i`) and is preserved by the initial left sweep (it lies strictly left of `hN`). Thus

~~~lean
Tsetup (hH-i) = T (h-(3*a+16+i))
~~~

Apply `s1Config_left_cell` at source index `3*a+16+i`. The S1 left-facing prefix before the quotient has exact length `3*a+16`, so `sideBit_append` drops it and leaves `sideBit (binDec L (8*k) ++ lh) i`. Then `binDec_mulpow2` and `binDec_carryPrefix` reduce this to

~~~lean
sideBit (d1pow t ++ (d0 ++ (binDec ell q ++ lh))) i
~~~

which is the `hleft` premise of `lbinDecHRunTape_leftFacing`. In particular, the four H-run boundary facts listed above are just the first `3*t+3` cells of this same identity; the right-zero fact at `hN+1` is supplied separately by `s1M2Setup_suffix`.

The generic H-run tape is `lbinDecHRunTape t Tsetup hH`. Its required left-facing identity is:

~~~lean
(∀ i, Tsetup (hH-i) = sideBit (d1pow t ++ d0 ++ tail) i) ->
(∀ i, lbinDecHRunTape t Tsetup hH (hH-i) =
       sideBit (d0pow t ++ d1 ++ tail) i)
~~~

This has a clean three-region proof:

1. `i<3*t`: use `sweptRightB_block`; when read head-facing, its physical `false,false,true` triples are exactly `d0pow t`. The final partial-block case uses the `hH+1` bridge write.
2. `i=3*t,3*t+1,3*t+2`: use `lbinDecHRunTape_d1` (the two bridge writes plus the original third one).
3. `i>=3*t+3`: the H-run preserves the far-left exterior, and both input/output streams reduce to the same `tail` cell.

The fixed postlude ends at state E, head `hN+2=hH+16`. Its output frame is the word with marked offsets `{13,11,8,5,2}` on `hN-12 .. hN+1`. Read head-facing from `hN+2`: the head cell is true (from the shifted initial-sweep block), the next three cells are exactly `markerWord 1`, and the next twelve cells are `d0pow 4`. The final bit of those twelve is at `hH+1`, supplied by `lbinDecHRunTape_rightPlus1`: it is the last B-sweep block when `t>0`, and the `afterLIncBridge` write when `t=0`. Hence the bridge/postlude output word at this head is:

~~~lean
[true] ++ markerWord 1 ++ d0pow 4 ++ d0pow t ++ d1 ++ tail
~~~

After the first E-scan step, the head is `hN+3`; the same word is then read as

~~~lean
[true] ++ markerWord 2 ++ d0pow (4+t) ++ d1 ++ tail
~~~

because `markerWord 2 = [true] ++ markerWord 1`. This is the alternate cut recorded in the earlier M2 residue-zero candidate note. Continuing the remaining `3*a-1` E-scan steps gives the final q4 source-left word below.

Reassociate `d0pow 4 ++ d0pow t = d0pow (4+t)`.

## 3. E-scan and exact q4 source-left word

The initial `3*a+2` left sweep leaves `3*a+2` consecutive ones in the shifted block. The setup/H-run/postlude only affect cells at or left of `hN+1`; the E-scan starts at `hN+2`, so the next `3*a` cells are still one. The existing `E_scan` therefore moves from state E at `hN+2` to state E at the original head `h=hN+2+3*a`, without changing the tape.

At that head, the exact q4 cut left-facing word is:

~~~lean
Q = [true] ++ d1pow a ++ markerWord 1 ++
      d0pow (4+t) ++ d1 ++ binDec ell q ++ lh
~~~

Using `binDec L (8*k-1) = d0pow (t+3) ++ d1 ++ binDec ell q`, this is equivalently

~~~lean
Q = [true] ++ d1pow a ++ markerWord 1 ++
      d0 ++ binDec L (8*k-1) ++ lh
~~~

Now the q4 suffix target identity is exact:

~~~lean
s1LeftFacing L (8*k-1) 1 (a+b+2) (2^b-1)
  = d0pow b ++ d1pow 2 ++ Q.drop 1
~~~

It follows from `binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2)`, `d1pow (a+2)=d1pow 2 ++ d1pow a`, and `d0 ++ d0pow (t+3)=d0pow (t+4)`. This is precisely the `happend` argument expected by `q4_suffix_run_to_s1Config`.

## 4. Right q4 shape and exact cost

The original S1 right stream is `[false,true,true,true,false,false] ++ d1pow (b+1)`. The initial left sweep sets `h+1` to true and restores `h` to true on its second move; cells from `h+2` right are unchanged. The setup/H-run/postlude lie strictly left of `h`, and E-scan does not modify the tape. Consequently the q4 suffix input has:

- ones at `h .. h+4`;
- zeros at `h+5,h+6`;
- `3*(b+1)` ones from `h+7`;
- blanks from `h+10+3*b` onward.

This gives both `q4RightShape` and the required blank far-tail premise.

The source run decomposes as:

~~~text
initial D sweep       9*a + 6
fixed setup                  44
generic H-run           12*t + 4
fixed postlude                 14
E scan                   3*a
q4 suffix               39 + 3*b
--------------------------------
total             107 + 12*a + 12*t + 3*b
~~~

Since `v2(8*k)=3+t`, `resetPrefixCost 2 (8*k) a b = 71+12*(a+3+t)+3*b`, exactly the displayed total. The q4 suffix produces `s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`; the existing counted-drain theorem then gives the full proposed increment.

## 5. Existing pieces vs remaining Lean work

Already present:

- `s1M2Setup_suffix`, `m2ZeroInitialSweep`, and `m2ZeroInitialSweep_Setup` in `M2EvenResidueZeroSource.lean`;
- the exact 44-step setup, `12*t+4` H-run, and 14-step postlude composition in `M2EvenResidueZeroFrames.lean`;
- `CountedLBinDecHRun.lean` with `sweptRightB_block`, `lbinDecHRunTape_d1`, and `lbinDecHRunTape_preserves_right`; the new uncompiled `LBinDecHRunLeftFacing.lean` drafts the three-region left-facing identity and the rightmost-boundary lemma;
- `CountedSweep.lean` with `E_scan` and the shifted initial-sweep block;
- `Q4RightEndpoint.q4_suffix_run_to_s1Config` and `s1Config_reset_prefix_then_counted_drain`.

Still to formalize:

1. exact-import compilation/axiom audit of the drafted generic three-region H-run left-facing identity and `lbinDecHRunTape_rightPlus1` in `LBinDecHRunLeftFacing.lean`;
2. the source-side H-run premises from the factorized quotient stream;
3. the postlude-frame + H-run boundary word `markerWord 1 ++ d0pow 4`;
4. the E-scan source-left word `Q`, q4 right shape, and far tail;
5. the `happend` list identity, reset-prefix cost equality, and final counted-drain composition.

The candidate all-q theorem remains `m2Even_residue0_reset_prefix_source` with cost `107+12*a+12*v2(k)+3*b`. This document establishes the intended exact word-level proof path, not its Lean acceptance.
