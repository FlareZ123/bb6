# Reparameterizing the A=1/A=2 q4-tail residuals as reset inputs

**Status:** exact encoder/algebra reduction from the current Type-C and 34-step residual formulas. This is not a compiled Lean theorem, not a completed reset itinerary, and not a halt proof.

## Source convention

In `im-results/agent8-s1-encoder/S1Encoder.lean`,
`s1Config L n m a z b h` is definitionally

```lean
s0Config (markerWord m ++ d0 ++ binDec L n ++ lh) a z b h
```

The source identities include `binDec_zero L = d1pow L`,
`binDec_even`, and `binDec_odd`. The local q4-tail modules already prove the useful special case

```lean
binDec k (2^k - 1) = d0pow k
```

as a private helper.

## A=1 Type-C residual

Agent 24's exact post-drain residual is

```text
s0Config (markerWord 0 ++ d0 ++ d0pow(L+3) ++ lh) a 0 b H
```

Set (k=L+3) and (n_0=2^k-1). Since
[
  \operatorname{binDec}(k,n_0)=d_0^{k},
]
this configuration is exactly
[
  s1Config\ k\ n_0\ 0\ a\ 0\ b\ H.
]

Thus the A=1 tail is not a malformed terminal word: it is the *maximal outer-counter* S1 reset input at width (k=L+3).

## A=2 34-step residual

Agent 24's exact residual is
[
\ell_{34}=d_1^K\Vert markerWord(0)\Vert d_0^2\Vert d_1^2
  \Vert d_0^{L+1}\Vert lh.
]

Set (k=L+4), (n_0=2^k-7). Repeated application of the source
`binDec_even`/`binDec_odd` recurrences gives
[
\operatorname{binDec}(k,2^k-7)
 = d_0\Vert d_1\Vert d_1\Vert d_0^{k-3}.
]
Since (k-3=L+1),
[
d_0^2\Vert d_1^2\Vert d_0^{L+1}
 = d_0\Vert\operatorname{binDec}(k,n_0).
]
Consequently the A=2 post-drain configuration is exactly
[
  s1Config\ k\ n_0\ 0\ a\ 0\ b\ H.
]

So the A=2 residual is also a canonical S1 reset input, now with width
(k=L+4) and outer counter (n_0=2^k-7). The reduction is algebraic;
it does not assume that the machine has already executed the reset.

## The next source step is explicit

Both starting counters are positive and odd, hence (v_2(n_0)=0).
The general source-run candidate
`OuterLCIncPostludeSource.outerLCInc_full_run` is therefore the
right one-step reset prefix to apply at either endpoint. For marker 0,
the parameter update dictated by the reset interface is
[
(k,n_0,0,a,0,b,H)
\longmapsto
(k,n_0-1,2,a+b+1,2^b-1,0,H+5+3b),
]
before the counted S0 drain. The subsequent counted drain transfers
(2^b-1) from the inner counter to the right counter, restoring the
(z=0) input shape for the next reset. This is precisely the repeated
Rst0/Rst2/Rst1 mechanism, not a direct list equality
(d_0^{L+c}=d_1^L).

The current `OuterLCIncCanonicalEndpoint.lean` only identifies the
nested frame for the special case (m=2,n=1). It does not yet prove
the marker-0 instances above, nor the all-parameter endpoint equality
needed to iterate the reset.

## Marker arithmetic at the end

If the reset recurrence is iterated from marker 0 down to outer counter
zero, the marker update (m\mapsto(m+2)\bmod3) gives final marker
(2n_0\bmod3). For both residuals,
[
n_0\equiv 2^k-1\pmod 3,
]
because (2^k-7\equiv2^k-1\pmod3). Hence:
- if (k) is even, the final marker is 0;
- if (k) is odd, the final marker is 2.

For the authentic later A=2 root branch, the relevant width is
`tm63Length1=76` (see `im-results/agent44-tm63-middle/README.md`
and `im-results/agent42-outer-lcinc/TM63Length1Parity.lean`), not
the initial blank-root width 3. Thus (k=L+4=80) is even, and this
marker arithmetic predicts final marker 0, consistent with the
marker-0 `TerminalEncoderBridge.s0_reset_sectionBits` interface.
This removes the parity objection for the authentic A=2 width, but
does not prove the canonical endpoint, the repeated reset chain, or
the terminal run.

## Research consequence

The sharp terminal gap is better expressed as:

1. prove the q4-tail-to-S0 adapter for the selected branch;
2. identify its post-drain output with the explicit S1 reset input above;
3. obtain the general marker-0 one-step canonical endpoint for
   `outerLCInc_full_run` (the source run itself is already parameterized);
4. compose the counted reset recurrence to (n=0);
5. prove the appropriate terminal interface for the resulting marker.

This replaces the ambiguous phrase “convert (d_0^{L+3}) to (d_1^L)”
with an exact source-counter starting state, a concrete one-step
transition target, and the remaining marker/terminal obligation.

No claim is made that steps 1, 3, 4, or 5 have been proved in this file.
