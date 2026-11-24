# Arbitrarily delayed halting from every fixed D unary counter

**Scope:** prepared finite tapes, not the four blank roots. Checked locally with Lean 4.36.0-rc2 using the original literal machine Boundary and original CryptidSix/CryptidTriplePairs. Both final theorems use only propext and Quot.sound.

Let sec(n,w) be the F/0 configuration with blank left and right word 1^n w. For every n>=2 and t>=0 there exists a finite suffix w beginning with 0, |w|<=3t+13, whose run makes j>=t positive live F/0-to-F/0 macro transitions and then halts for the first time at u. With N the final unary counter and k its terminal parameter,

    8^j (n-1) <= 3^j (N-1)
    N <= 3k+4
    u > r + 12k^2, r>=j

where r is the total raw duration of the live prefix. Thus the maximal finite halting time over suffixes of length L for each fixed n grows at least as a constant (depending on n) times (8/3)^(2 floor((L-13)/3)) as L tends to infinity. The root-specific BB(6) lower bound does not change.

## Proof

Use P(q,p,Y)=(01)^q 0 1^p Y and H=1101101100. The following are literal-source return transitions, for arbitrary finite tails:

- E: n=3k+4, P(q,p+3,Y) -> (8k+9,P(q+2,p,Y)).
- B with a pair: n=3k+2, P(q+1,p,Y) -> (8k+10,P(q,p,Y)).
- B without pairs: n=3k+2, P(0,l,0W) -> (8k+9+l,0W).
- A: n=3k+3, P(q,0,0W) -> (8k+11+2q,W).

For n of A or E type P(q,0,H) halts exactly after 12k^2+41k+101+2q or 12k^2+41k+106+2q respectively. This uses the same terminal word and finite transition checks already known in AHaltCylinder and AllQFirstHalt; the new content is the recursive construction, not those terminal words.

Prove by induction on t that for every q,n>=2 there exist p,Y with p+|Y|<=3t+12 and at least t returns followed by halt. At t=0, A/E use H. B with q>0 recursively consumes a pair; B with q=0 chooses l in {0,1} to make 8k+9+l an A or E counter, with remaining suffix 0H. For t+1 choose the respective next counter and pair count, apply induction, and prepend the corresponding packet: E costs 3 extra bits, B with pairs costs none, B without pairs costs 1 and A costs 2. Every return has 8(n-1)<=3(N-1). Set initial q=0 for the stated length bound. First-halt exactness uses the literal frozen state 6 and the demonstrated last-live state 5.

The construction certifies at least j positive macro endpoints, not that every such macro is the first physical return; no first-return minimality assumption is needed for the time bound. Trailing explicit blank zeros are allowed. It strengthens the previously known existence of halting extensions at fixed n (which does not give arbitrary delay), but cannot determine whether any authentic blank root ever hits a terminal configuration.

## Reproduce

Archive Proofs.tar.xz.b64 decodes to SHA256 c8046d74afb2a254d486e9eeadcb29b9634e41009a3ebd561a5357d2d219d99d. The two Lean files have SHA256 f94d5c83238572c059aaabffe9fa61f805104777ebbd13090c3b6dc4c276087a and 3e9a467287291c9b56ba78eab8cc8f4c45447bade33965640d21b117f32e92a8. Run reproduce.sh from a repository checkout with lean on PATH. Original sources: Boundary decompressed SHA256 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883, CryptidSix git blob ac46590a8049a412671544a9319cb0aaf2b2c257, CryptidTriplePairs blob db15d8dc6da42f17faa952c751c4c849b081e1dd. All three dependency modules and both new modules compiled locally. No CI requested.

Final theorems DDelay.fixed_counter and DDelay.source_fixed_counter. No change to the root coverage ledger.
