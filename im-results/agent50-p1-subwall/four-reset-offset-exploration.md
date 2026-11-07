# Four-reset shifted-wall extension: algebraic exploration

**Status:** exploratory derivation only. This note is not a Lean theorem and must not be cited as a proved reset floor. It records a possible route from the verified five-reset floor to a six-reset floor.

## Starting point

To raise the right-five floor from five to six, the depth dichotomy reduces the low branch to a genuine four-positive-reset prefix on the exact wall `b+4*m+4*n+20=12P`, where `P=2^n` and `n>=14`.

Peel its final positive reset. The same mass and inverse-power calculation used in `ThreeResetWallPrefix.lean` gives:
- reset depth 1: `d3+6P=10*m3+10*n+47`. Since the three-reset prefix cost satisfies `m3<=7n+10`, this is negative under `P>=1100n`, so depth 1 is impossible;
- reset depth 2: the predecessor is a genuine three-reset prefix with the *offset wall* `b3+4*m3+4*n+20=12P-16*(m3+n+6)`.

Combining this offset wall with the mass equation `b3+d3+2*m3+2*n+13=14P` gives
`b3=12P-20*m3-20*n-116`,
`d3=2P+18*m3+18*n+103`,
and therefore `C3=d3-1=2P+18*m3+18*n+102`.

## Peeling the next two resets

Let `m3=m2+t3+1`, where `m2<=5n+7` is the cost of the two-reset prefix.

The predecessor-wall relation is `b2+4*m2+4*n+20 + 2^(t3+1)*C3 = 28P`.

The same bound `d2+b2/2+3<=14P` and `C3>=2P` forces `t3<=2`.
- If `t3=1`, algebra gives `d2+6P=74*m2+74*n+559`. The cost bound gives `d2+6P<=444n+1077<6P`, contradiction.
- If `t3=2`, algebra gives `C2=c2+3=2P+146*m2+146*n+1254`.

Now let `m2=m1+t2+1`, where `m1<=3n+4` is the cost of the one-reset prefix. The same predecessor-wall argument forces `t2<=2`.
- If `t2=1`, algebra gives `d1+6P=586*m1+586*n+6191`. The cost bound gives `d1+6P<=2344n+8535<6P`, contradiction.
- If `t2=2`, algebra gives `b1=12P-1172*m1-1172*n-13556` and `d1=2P+1170*m1+1170*n+13543`.

The cost bound `m1<=3n+4` and `P=2^n` imply `b1>=12P-4688n-18244>=6P` for all `n>=14`. Since the first zero-depth tail obeys `2^s1*(b1+12)<=14P`, this forces `s1<=1`.

## Remaining root cases

The first reset inverse relation is `L=D+B/2+3=2^u*(c1+3)`. The root equations remain `B+D+2*r+2*n+13=14P` and `2^r*(B+12)+2*n+4=14P`, with `r<=m1<=3n+4`.

There are two tail cases.

### Case s1=0

Then `c1+3=d1-1`, so `C1=2P+1170*m1+1170*n+13542`.

Useful bounds are `2P+1170n+15882 <= C1 <= 2P+4680n+18222`. Also `L<=14P` and `C1>=2P`, so `u<=2`. Thus only exact equalities `L=2*C1` and `L=4*C1` need to be excluded.

The root equations give:
- `r=0`: `L=7P-n-2`. Equality `L=2*C1` reduces to `3P=2340*m1+2341*n+27086`; `L=4*C1` is impossible by sign.
- `r=1`: `2L+3n+10=21P`. The two possible equalities reduce to `13P=4680*m1+4683*n+54178` and `5P=9360*m1+9363*n+108346`.
- `r>=2`: the root equations give `8L+16r+14n+28>=98P`. With `r<=3n+4`, a sufficient inequality for `4*C1<L<8*C1` is `34P>149822n+583196`, which holds from n=18 onward. The finite cases n=14,15,16,17 still need a formal treatment, likely using the root divisibility equation and `B%4=0`.

### Case s1=1

The one-step `UpperTail` transition gives `d1=c1+j+6`, while the root dyadic equation gives `2j+8=14P-2n-4`, hence `j=7P-n-6`. Therefore `C1=c1+3=-5P+1170*m1+1171*n+13546`.

For n>=15, the bound `m1<=3n+4` makes this negative, so s1=1 is impossible. At n=14, positivity forces `m1 in {45,46}`. Here `P=16384`, and `B+12` divides `14P-2n-4=229344=2^5*3*2389`. Together with `B%4=0`, this forces `r<=3`.

The four possible root lengths for r=0,1,2,3 are `114672, 172006, 200672, 215004`. For `m1=45`, `C1=670`; the only power-of-two multiple of 670 in this length range is `256*670=171520`, which is absent. For `m1=46`, `C1=1840`; the only power-of-two multiple in the length range is `64*1840=117760`, which is absent. This finite exact check still needs to be formalized in Lean.

## What remains to prove

1. Formalize the fourth-reset peel and the offset-wall source equations from the original `CountCone` extraction.
2. Formalize the `s1<=1` bound and the one-step right-coordinate identity for `s1=1`.
3. Prove the s1=1 finite n=14 cases with Lean, not a handwritten table.
4. Build a root-power core for s1=0, including the finite n=14..17 cases and the n>=18 inequalities.
5. Only after all of the above compiles against the exact source modules may a six-reset floor be claimed.

The exact-wall theorem `source_no_three_reset_shifted_wall` does not apply directly to this offset wall. A parameterized or separately derived offset-wall theorem is required.
