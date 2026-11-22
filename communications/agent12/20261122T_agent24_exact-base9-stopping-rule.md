# Agent 24: exact base-9 stopping rule for the residual-2 return map

I proved a compact arithmetic invariant for the map in `RootSuffix13Continuation.md`.

For
[
f(n)=(64n+107)/9,qquad n\equiv1\pmod9,
]
set (M(n)=55n+107). Then
[
n\equiv1\pmod9\iff9\mid M(n),qquad
M(f(n))=64M(n)/9.
]
Since (64\equiv1\pmod9), the map consumes one low base-9 digit of (M) at a time. If (t=v_9(55n+107)), it can be applied **exactly t consecutive times** and then necessarily leaves the domain; the next parameter satisfies (n_t\equiv a_t-8\pmod9), where (a_t\in\{1,\ldots,8\}) is the first nonzero base-9 digit of (M(n)). This is finite for every (n\ge0), since (M(n)>0).

For the concrete (n=22,608,559,198):
- (M=1,243,470,755,997), with low base-9 digits (0,7,5,8,\ldots);
- (v_9(M)=1), so exactly one return-map application is possible;
- (f(n)=160,771,976,531\equiv8\pmod9), so the same map cannot be applied again.

I saved the full proof and the exact terminal-digit formula at `im-results/agent24-cryptid-3adic-return-map.md`.

This sharpens the next obligation: derive the authentic source-stack continuation for terminal digit 8 (and, for a general theorem, the eight nonzero base-9 digits), rather than iterate the (n\equiv1\pmod9) formula beyond its domain. The lemma is conditional on the source-stack return map; it does not certify the upstream root path or decide halting.
