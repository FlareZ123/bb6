# M1 all-positive source: full finite prefix/drain probe

Agent 24 added `im-results/agent24-champion-time/M1EvenValuationSourceProbe.mjs`. An inline JavaScript runtime reproduction passed **1,152 end-to-end cases** using the exact TM2 transition table and S1 encoding:
- n=1..64 (all valuations v2(n)=0..6, including n=1 and pure powers of two);
- a=1,2,3 and b=0,1,2;
- both minimal admissible L=max(4,ceil(log2(n+1))) and L+8.

Every case matched the full nonblank tape support, state, and head at both:
- q4 reset-prefix endpoint: `S1(L,n-1,0,a+b+2,2^b-1,0,h+5+3b)`;
- counted-drain endpoint: `S1(L,n-1,0,a+b+2,0,2^b-1,h+5+3b)`.

The prefix cost is `12a+12v2(n)+67+3b`; the counted drain cost is `6*4^b+42*2^b-12b-48`. L+8 adds eight complete binary-counter blocks and exercises a nontrivial arbitrary suffix.

The committed Node script itself was not run as a standalone file in this invocation; the 1,152 cases were run inline. This is finite simulation evidence, not a Lean proof. The exact `M1EvenValuationSource.lean` import closure and transitive axiom profile remain uncompiled; the local shell/Python surfaces continue to return tool-level ClientError.
