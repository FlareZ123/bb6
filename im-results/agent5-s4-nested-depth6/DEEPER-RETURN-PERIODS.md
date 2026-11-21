# S4 deeper suffix return maps: an eventual 15-digit period

**Status:** exact finite BigInt computation and exact boundary-word factorization; not a proof of nonhalting or of BB(6).

This note extends the six-level Q/R/V/W/X/Y reduction in `README.md` and `s4_nested_depth6.mjs`. It identifies two further all-suffix return maps and an eventual period for the first 15 digits of the reduced stack.

## 1. Conventions and scope

A reduced stack is written `[d_0,d_1,...]`. A finite gate word `G_w` is the sequential action of its offsets. Write `B_p` for addition of `p` to the first digit. The new skewed return map has the form

[
F = B_p\circ G_w.
]

If the prefix after which the map acts returns after several blocks, boundary extraction emits a new suffix word and may leave a final pending head addition. That pending addition must be retained; dropping it changes the map.

For composition, if `F = B_p ∘ G_w`, then
[
F^m = B_p\circ G_{w^{(p)}}^{,m-1}\circ G_w,
qquad
w^{(p)}=(w_0+p,w_1,\ldots,w_{|w|-1}).
]
Thus the first block is unshifted and each subsequent block has only its first offset increased by `p`.

The generic boundary decomposition is supported by `im-results/agent5-s4-prefix-causal/S4BoundaryWord.lean` and `S4SuffixBoundary.lean`. The new concrete word extraction and prefix-period scans are reproduced by `s4_nested_depth6.mjs`. The numerical scans use exact JavaScript `BigInt`; the concrete Y/Z/F word data and the period scan are not yet separately certified in Lean.

## 2. Two further return maps

Let (N_Y) be the number of underlying P-returns represented by one Y block:
[
N_Y=1,125,899,906,842,624,000,000.
]

The existing Y word has 18,084 gates and acts after the eight-digit prefix.

### Ninth digit: (Z=Y^5)

The first digit of the suffix after one Y block (the ninth digit of the full reduced stack) has the exact five-cycle
[
egin{aligned}
24289203005747258389 &\to 24289203005747258391\
&\to 24289203005747258388\
&\to 24289203005747258390\
&\to 24289203005747258392\
&\to 24289203005747258389.
end{aligned}
]

Extracting five Y blocks on that one-digit prefix gives a pure suffix word (Z), with no pending addition:

| Map | Gates | Underlying P-returns | Offset sum |
|---|---:|---:|---:|
| Y | 18,084 | (N_Y) | 1,152,921,504,606,846,975,963,832 |
| Z | 45,157 | (5N_Y) | 5,764,607,523,034,234,879,909,686 |

Both satisfy the exact mass identity
[
sum_i w_i+2|w|=1024N.
]

### Tenth digit: (F=B_{p_F}\circ G_{w_F})

The first digit of the suffix after Z (the tenth full-stack digit) has an exact four-cycle under Z:
[
73515085360333450331
	o 73515085360333450333
	o 73515085360333450329
	o 73515085360333450332
	o 73515085360333450331.
]

Extracting four Z blocks gives the skewed return map (F):
- (|w_F|=90,309) gates;
- (p_F=73,515,085,360,333,450,329);
- (sum_i (w_F)_i=23,058,356,577,051,579,186,369,053);
- (F) represents (20N_Y=22,517,998,136,852,480,000,000) underlying P-returns.

The pending-aware mass identity is exact:
[
sum_i (w_F)_i+2|w_F|+p_F
=23,058,430,092,136,939,520,000,000
=1024(20N_Y).
]

The first digit of the suffix after the tenth digit has a four-cycle under F. Starting from the suffix before the first F application, its values are
[
194476509727446559354
	o 194476509727446559355
	o 194476509727446559353
	o 194476509727446559352
	o 194476509727446559354.
]

## 3. Prefix periods below the F return map

Start the F iteration at the suffix **after one F application**. A full-stack BigInt scan of 1,280 further F blocks gives the following first-repeat periods for prefixes of the suffix after the tenth digit:

| Suffix digits tracked | Full-stack prefix period under F |
|---:|---:|
| 1 (full digit 11) | 4 |
| 2 (full digits 11–12) | 16 |
| 3 (full digits 11–13) | 64 |
| 4 (full digits 11–14) | 320 |
| 5 (full digits 11–15) | 1,280 |

Every listed period has preperiod zero from that post-F starting state. The scan applies the full skewed word to the full suffix at each block, not a truncated prefix simulator. It finds no halt in these 1,280 F blocks. The stack length increases from 23 to 28 at F block 12; therefore the full state is not claimed to be periodic.

The first five suffix digits at the start of this prefix cycle are
[
egin{aligned}
(&194476509727446559355,\
&668971700564857346826,\
&1934094707247186541779,\
&1149120246030680941703,\
&5832425563795378288919).
end{aligned}
]

## 4. Consequence for the first 15 digits

The nested return structure gives a witnessed eventual period for the first 15 digits of the reduced stack:

1. Five Y blocks return the ninth digit and induce Z.
2. Four Z blocks (20 Y blocks) return the tenth digit and induce F.
3. One F block places the 11th–15th digit prefix at the start of the observed F-prefix cycle.
4. The 11th–15th prefix returns after 1,280 F blocks. Since one F block is 20 Y blocks, this is 25,600 Y blocks.

Thus, measured from the state after the first Y block, the first-15-digit projection reaches this cycle after 25 additional Y blocks (one-based Y block 26), and has a witnessed period of **25,600 Y blocks**.

In the reduced P-return units, these counts are:
- preperiod witness: (25N_Y=28,147,497,671,065,600,000,000);
- period witness: (25,600N_Y=28,823,037,615,171,174,400,000,000).

The 9th–15th digits at the cycle start are
[
egin{aligned}
(&24289203005747258389,\
&73515085360333450331,\
&194476509727446559355,\
&668971700564857346826,\
&1934094707247186541779,\
&1149120246030680941703,\
&5832425563795378288919).
end{aligned}
]

This is a projection period only. The suffix after digit 15 continues to evolve, and the observed growth at F block 12 rules out treating the whole stack as periodic. The earlier 10,001-Y-block scan could not reach this 25,600-Y-block first-15-digit return; its failure to find a 30-digit cycle is therefore unsurprising and remains unresolved.

## 5. Interpretation and next work

The exact period sequence (4,16,64,320,1280) is consistent with a mixed-radix odometer: powers of four in the first three tracked suffix digits, followed by a factor of five. This is a structural hypothesis, not yet an all-depth theorem.

The highest-value next work is to:
1. extend the exact F-prefix period scan to the 16th and later digits and determine the recurrence rather than assuming it;
2. derive an inductive description of the boundary words and their pending additions;
3. connect prefix-period growth to a monotone tail-growth or nonhalting invariant;
4. formalize the concrete Y/Z/F extraction and finite prefix-cycle certificates in Lean.

**No BB(6) value, universal upper bound, or nonhalting proof is established here.** This is an intermediate computational result and belongs in `im-results/`, not `results/`.
