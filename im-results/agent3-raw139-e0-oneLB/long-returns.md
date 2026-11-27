# OneLB long final-hole executions (discovery; source proof pending)

Four previously unresolved one-hole leaves now have exact primitive replays to the final hole.

| C1 code | original residual / extension | table | live steps before query | queried slot |
|---|---|---|---:|---|
| 9 | 209 | 7,20,11,1,14,9,17,16,6,11,0,24 | 31790091 | F1 |
| 9 | 212 / ordinary move 0 | 7,24,11,22,14,9,17,16,6,11,16,0 | 125150404 | A1 |
| 9 | 218 / ordinary move 0 | 7,24,11,22,14,9,17,16,6,11,15,0 | 187672020 | A1 |
| 21 | 892 | 7,23,11,13,14,21,24,16,6,11,3,0 | 3643339 | D0 |

The two A1 machines share an exact return map at C reading the first blank right of the tape, with a 1 immediately left. Let U be the reversed left tape, initially 11 followed by infinitely many zeroes (after two steps). Write U = 1 v d W, where v is a concatenation of tokens b=1 and a=010, and stop at the first delimiter d = 00, 0110 or 0111. This greedy parse always terminates on eventually-zero tapes. Put phi(b)=0 and phi(a)=100, extending by concatenation. For d=00 the next frontier is U'=10 phi(v) 101 W. For d=0110 the next frontier is U'=10 phi(v) 10011 W. Each E scan consumes b in 3 steps; a in 3 steps for F0=0LE or 7 steps for F0=1RD. The right C scan complements the intervening word and adds the next frontier 1. The total return costs are 12 + (8 or 12)*#a + 4*#b, with +4 for d=0110. For d=0111 the execution reaches A1 after 5 + (3 or 7)*#a + 3*#b steps rather than returning. The return map matches direct primitive frontier simulations; the 7656th complete return reaches frontier at times 125135054 and 187636254; next parse has a=5104,b=11 and delimiter 0111. Thus query times are as tabulated, both head -14. Counts across completed returns: a=15625300, b=10192, stop00=7653, stop0110=3. Independent full primitive simulations confirm both times and exact slot. The other two times were directly simulated, not inferred from the shared return map.

Use a certified accelerated packed sweep checker (finite local arbitrary-tail transfer lemmas, repeated transfer composition, exact packed arithmetic) rather than millions of individual primitive replay chunks. No claim of Lean acceptance yet. The previously unresolved C1=0RA residual 286 is now independently source-checked nonhalting by Agent12's [growing binary counter induction](../agent12-raw139-oneLB-c1-286/README.md). Its exact table is [7,21,11,13,14,1,24,16,6,11,16,11]. The source proof is grafted into the code-1 candidate; whole-child and parent acceptance remain separate.

