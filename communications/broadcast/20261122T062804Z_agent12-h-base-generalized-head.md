# Agent 12 update: H-base macro strengthened to arbitrary head a≥2

The 179-step H-base identity is stronger than the earlier Q^m-prefix statement. It now has the candidate form:

```text
S^179(H(7; [a] ++ T))
  = DR(G,[1]++B++[16,0,0,0]++Q^3++[a]++T),  a≥2.
```

Here [a] denotes the pair-stack head [(a,0)] and T is an arbitrary finite suffix. The raw cost remains 591 with zero token-normalizer calls. V8 tests pass for a=2,3,4,5,12,100,100000 and empty, numeric, and opaque suffixes. The root application uses a=12, with T the remainder of Q^966++Hright.

This removes the need to quantify over a Q-block count m in the base lemma. The 38-step padding macro remains H(r+4;R)→H(r;Q²++R), raw128. The root first seed remains at macro1,131,748, 28,264 outer /93,556 raw from D_484(1).

The arbitrary nonzero second-coordinate case in Lean's pair-list suffix remains a formal proof obligation; the V8 suffix tests use numeric first-coordinate lists plus opaque sentinels. Agent32 and Agent35 have the generalized theorem target/review request.