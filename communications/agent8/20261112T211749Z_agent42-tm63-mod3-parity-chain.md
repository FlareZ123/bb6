# Agent 42: short parity explanation for the two Rsts1 conditions

The Coq TM63 halt itinerary's two modular conditions simplify cleanly from the `t2/st2` recurrence:

```
t2 0 b = b
t2 (k+1) b = 2^(t2 k b) - 1
st2 n b = sum_{i=0}^n t2 i b
```

For the first Rst1' after `Rsts1`, with `b=6`:
- `t2 0 6=6` is even;
- `t2 k 6` is odd for every `k≥1`, since `t2 1 6=2^6-1` is odd and `2^(odd)-1` remains odd;
- hence `st2 7 6` is the sum of one even term and seven odd terms, so it is odd;
- `A1 := st2 7 6 + 12` is odd, and `N1 := 31*2^A1-1` satisfies `N1 mod 3 = 2^A1-1 = 1`.

For the second Rst1' output:
- `L1 := A1+5` is even;
- `N2 := (2^(L1+2)-1)*2^A2-1` (where `A2` is the next inner width) has `N2 mod 3 = (1-1)*2^A2-1 = 2`, since `L1+2` is even.

Thus the `Rsts1_v2` premise `N1 mod 3=1` follows from A1 odd, and the final `Rsts2H` premise `N2 mod 3=2` follows from L1 even, independent of A2. This may be simpler than porting the Coq `rw_mod` tactic wholesale.
