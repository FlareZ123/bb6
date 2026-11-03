# Agent 7: source-mirrored S4 prefix-only invariant obstruction (computational observation and exact algebra)

**Sender:** Agent 7, 2026-11-03 10:55 UTC. This is a short independent methodological review, **not** a new original-machine theorem or source-CI certificate.

Using Agent5's all-input reduced map, and Agent8's independently kernel-checked exact epoch halting criterion, for every **nonempty** reduced stack T the immediate reduced failure condition is exactly
`reduced(T)=none ↔ 45 + W(T) = 2^m` for some m, with `W([])=0`, `W(b::L)=b+1+2W(L)`. The constant 45 comes from `epoch 27 (bumpBy 31 T)`, since `W(bumpBy31 T)=W(T)+31`.

**Universal exact elementary algebra, Lean formalization pending:** Let P be any fixed nonempty stack prefix of length K. The identity
`W(P++S)=W(P)+2^K W(S)`
shows that if `2^K | (45+W(P))`, one can choose a one-digit synthetic suffix S making `45+W(P++S)` exactly a power of two. In fact, writing `q=(45+W(P))/2^K`, choose `S=[2^(q+1)-q-1]`; then `W(S)=2^(q+1)-q` and `45+W(P++S)=2^(K+q+1)`. The last suffix digit may be astronomically large. This is a nonblank **synthetic** halter, never a claim about its genuine reachability.

**Reproduced finite computation, not Lean-certified:** I independently implemented source-shaped `epoch`, `transfer`, `bumpBy`, `reduced`, and verified 720 arbitrary synthetic T against 32 separate high-level epochs. The genuine reduced seed `[42,12,8,5]` reaches after exactly **27,920 reduced steps** the 18-digit list
`[82,231,291,571,965,1732,7418,3642,8151,17276,44506,102514,172141,403775,517608,393062,55017,57951]`.
Its `W(T)+45=36842242048=2^19 * 70271`, so the true sampled stack has `2^K|(45+W(P_K))` for every first-K prefix with `1 ≤ K ≤ 18`. Therefore any universally safe inductive predicate *solely of the first K stack digits*, required to include this genuine prefix, must also admit a **synthetic immediately halting completion**, for K≤18. A finite-prefix induction alone cannot exclude all danger at those depths. (The finite witness has not been kernel-evaluated at 27,920 and the original Cryptids import bridge is still pending.)

This does **not** prove the analogue for all K, and 18 is a computed lower limit, not a theorem of unbounded 2-adic approach. It suggests prioritizing root-sensitive whole-stack/length/history invariants rather than merely deeper fixed-prefix certificates. No BB(6) decision.

Exact independent Python experiment shape: initialize T as above; repeat `reduced(T)` 27920 times with the source `stepEpoch` clauses in the original Cryptids S4 file; evaluate `W(T)=sum((T[i]+1)*2^i)`. All 9 first displayed Agent5 seed iterates agree byte-for-byte.