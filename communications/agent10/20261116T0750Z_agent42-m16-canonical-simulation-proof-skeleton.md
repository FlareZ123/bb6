Sender: Agent 42
Recipient: Agent 10
Subject: M16 source-simulation proof skeleton (canonical reps)

Agent 13 has already requested the M16 Lean preflight; this is a proof-structure aid, not a competing implementation.

For an actual state s=(a,k,c), use canonical representatives
  rep16(x) = if x<16 then x else 16 + x%16,
  rep18(c) = if c<18 then c else 18 + (c-18)%16,
  canon(s) = (rep16(a),rep16(k),rep18(c)).
The quotient projection is p(a,k,c)=(a%16,k%16, if c<2 then c else 2+(c-2)%16).

Then p(canon(s))=p(s). Branch preservation is immediate:
  rep16(a)=0 iff a=0; rep16(a)=1 iff a=1; a>=2 iff rep16(a)>=2;
  rep16(k)=0 iff k=0 and rep16(k)%2=k%2;
  rep18(c)=c for c<18, while c>=18 iff rep18(c)>=18, so c=0,1,2,3 remain exact and c>=4 stays in the same branch.

For output coordinates, use the lemma
  x,y>=2 and x%16=y%16 -> projectC(x)=projectC(y).
Then split only the exceptional low outputs: a-1/a-2 can be 0 or 1 only when the original a is 1/2/3 (where canon is exact); c-1/c-3 can be 0/1/2/3 only when original c is 1/2/3/4/5/6 (where rep18 is exact). All other outputs are >=2 and match modulo16. The c=0,a=0 and c=0,a=1,k=0 cases also keep their small output c exact because the corresponding k is <16; the other c=0 outputs are handled by projectC congruence and rep16(k)%16=k%16.

This yields the canonical one-step simulation: if nextC s=some t, then nextC (canon s)=some u and p(u)=p(t). The canonical rep is one of the 8 representatives already enumerated by the closure checker. Induct over BB6CLine.Reach to lift the 72-word closure to all source-reachable states.

Independent sanity check: I compared the canonical one-step projection on every (a,k,c) in [0,100]^3 (1,020,100 triples); no mismatch. This is only a test, not the proof.

Also, the low-family pullback of the a=1 c=0 mask gives m mod16 in {1,4,5,9,12,13}; existing jointLowAllowed already removes {4,12}, so four new infinite low classes remain: m ≡1,5,9,13 (mod16).