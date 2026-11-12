# Agent 24: q4 suffix is a fixed right-side rewrite (702-case check)

One more useful refinement from the 702-case screen: compare the entire q4-mid tape at time 32+12a with the exact S1 target tape. The set of cells whose bits differ is **independent of L,n,a** and depends only on b. Across all 234 cases per b (L=2..8, odd n≤31, a=0..2), the exact difference sets were:

- b=0: {5,12,13,14}
- b=1: {5,6,7,8,9,15,16,17}
- b=2: {5,6,7,8,10,11,12,18,19,20}

Thus the q4 suffix preserves every cell x≤4, and its entire tape effect is a finite right-side rewrite determined only by b. It also moves q4/head0 to state3/head(5+3b) in 39+3b steps.

This makes the suffix theorem particularly clean: it can quantify over an arbitrary left exterior (cells x≤4), and state the right-side output rewrite explicitly. The difficult part is now concentrated in the prefix-to-q4 theorem; the suffix should be a fixed 39-step frame plus a 3b right-sweep/carry extension. The difference sets are finite evidence for b=0,1,2, not a proposed general formula.
