# S4 tenth-digit 703-carry attractor over the nine-prefix cycle

**Intermediate structural theorem, 9 November 2026.** This concerns the total, length-preserving S4 prefix projection `pp`, and conditionally the genuine blank-root orbit of the six-state machine `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. The result does **not** establish halting or nonhalting of S4 or BB(6). Its arithmetic is exactly reproducible in [tenth_carry_attractor.py](tenth_carry_attractor.py). The original-source correspondence is the earlier [all-depth prefix causality theorem](README.md); the nine-prefix periodicity has separately computed Lean chunk certificates, with final source-import composition [S4PrefixNinthCycle.lean](S4PrefixNinthCycle.lean) requiring a completed successful CI before it is called original-source certified.

## The new all-initial-value result

Let
[
p=(283,906,982,3490,3734,5935,13580,109210,171050)
]
and let `pp` be the previously verified total nine-/ten-digit projection of the authentic S4 `P=G(509);G(290);G(219)` return. Since `pp^[81920] p=p`, its action on a tenth digit defines `F:ℕ→ℕ` uniquely by
[
pp^{81920}(pmathbin{+!!+}[v])=pmathbin{+!!+}[F(v)].
]
The following **global, arbitrary-input** inequalities hold:
[
oxed{quadlfloor v/2^{703}floor+366445  le F(v)lelfloor v/2^{703}floor+366450quad}qquad(vinmathbb N).
]

The complete first-nine-digit block traverses the all-odd carry path exactly **703 times** across its 245,760 constituent `G` operations. The tenth-coordinate map at any stage is either `v↦v+d` or `v↦f(v+d)`, with nonnegative input-independent integer `d`, where
[
f(z)=egin{cases}z/2+2,&z {m even},\
(z-1)/2,&z {m odd}.end{cases}
]
The three-stage offsets and their order are reproduced from the source projection. The bound above uses **all stages**, including their exact additive shifts; it is much stronger than merely identifying nine periodic digits.

In particular, the full tenth-coordinate map has the following exact small-state table.

| Input `v` | `F(v)` |
| --- | --- |
| 366445 | 366447 |
| 366446 | 366449 |
| 366447 | 366446 |
| 366448 | 366448 |
| 366449 | 366445 |
| 366450 | 366447 |

Therefore **every initial natural tenth digit**, irrespective of deeper suffix values, eventually enters one of two terminal components under the *total prefix* block map: the fixed point `366448`, or the four-cycle `366445→366447→366446→366449→366445`. The two components are genuinely distinct, so full phase synchronization to a unique orbit is false.

For the verified S4 root state after 5,457 accelerated returns, the tenth digit is `366446`. Hence **provided the genuine S4 orbit continues to survive**, its tenth digit at times `5457+81920m` follows the four-cycle above, while the first nine digits return to `p`. In particular the first ten digits recur every `327680` reduced returns along a surviving root. This is a conditional blank-root statement; the original stopping gate remains open and may interrupt a block.

## Mathematical proof

For a length-nine vector `p` and offset `c`, begin with the active carry `a=p[0]+c`. If `a` is odd at position `i`, emit `floor(a/2)` and advance with `a←p[i+1]+floor(a/2)+1`. If `a` is even, emit `a/2+2`, update the following digit by `+a/2`, and stop scanning. This is exactly the recursive definition of the existing prefix `hp`/`gp`. It proves by induction that the first nine outputs ignore the tenth input, while the tenth output has one of the two scalar forms given above: a non-halving additive update when the scan stops in the first nine positions, or a `f` update if all nine positions have odd carries. The special non-halving update at the ninth position is `v↦v+a/2`; stopping earlier leaves `v` unchanged.

An all-odd scan of nine positions is equivalent to `(W(p)+c) mod 512=0`, where `W(p)=Σ 2^i(p_i+1)`. Indeed, when the active head is odd, dividing `W(p)+c` by two advances exactly to the next active carry plus the remaining weighted tail. Iterating proves the congruence equivalence. This also links the **703** half-drains to the existing 703 potential binary-power stopping phases. It is a congruence test, not an actual halting decision.

For the scalar update sequence, maintain the interval envelope
[
lfloor v/2^rfloor+ellle y(v)lelfloor v/2^rfloor+u.
]
Begin at `r=0, ell=u=0`. An additive `+d` replaces `ell,u` by `ell+d,u+d`. A half-drain replaces them by
[
r'=r+1,qquad
ell'=lfloor(ell+d)/2floor,qquad
u'=lceil(u+d)/2ceil+2,
]
using `floor(z/2)≤f(z)≤floor(z/2)+2` and elementary floor arithmetic. These are universally quantified inequalities at each stage, independent of the input digit. Running the **finite, exact** 81,920-return recurrence yields `(r,ell,u)=(703,366445,366450)` and verifies `pp^[81920] p=p`. The checker independently compares the scalar transfer formula against the ten-coordinate `gp` at every full odd carry and selected other positions, and verifies the six displayed exact return values.

Put `B=2^703`. For `v≥B`, the upper bound gives `F(v)≤floor(v/B)+366450<v`, so repeated applications must eventually reach `v<B` by well-founded descent. Then `F(v)∈[366445,366450]`, and another application enters the displayed five-point invariant set. The finite transition table completes the proof of the global attractor classification.

## Proof status, practical leverage, and open boundary

- **Exact mathematical derivation:** The scalar transfer and all-input envelope are elementary paper proofs, with a finite 245,760-stage coefficient certificate. The exact coefficients, carry count and six return values are checked by the committed deterministic Python file. This is a finite arithmetic certificate, **not yet a Lean kernel theorem** for the numerical constants.
- **Original machine connection:** Previous original-source CI established `S4PrefixCausal.prun_prefix` and the authentic root through return 5,457. The separately composed nine-period module must pass source CI before the unconditional source certificate for its period can be cited. The total-prefix contraction statement is independently valid as an arithmetic property of `pp`.
- **Research leverage:** The tenth coordinate at these block boundaries is globally eventually constrained to five values even from arbitrarily large synthetic input values. Root-specific selection of the four-cycle provides an all-time conditional prefix and an exact mass-flux decomposition one digit deeper than the eight-prefix result. The remaining digits carry the increasing stack mass, and the 703 candidate halting phases remain unclosed.
- **Remaining decisive question:** Determine an all-time invariant for the **genuine complete suffix** at those candidate gates. This finite-dimensional attractor theorem, including its second fixed-point basin, does not rule out synthetic power-of-two stopping completions or decide the authentic root.

To reproduce from the repository root, run the sibling Python file directly. No external data or random seed is required. The checked integers `703`, `366445`, `366450`, and the six transition values are asserted, with an immediate failure on mismatch.
