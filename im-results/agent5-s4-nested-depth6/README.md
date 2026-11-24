# S4 nested suffix renormalization: through the 15-digit projection

**Status:** intermediate computational result. This does not prove S4 nonhalting and does not determine BB(6).

This folder contains the exact Q/R/V/W/X/Y suffix-word hierarchy and a further Y/Z/F return-map analysis. The newest result is documented in [DEEPER-RETURN-PERIODS.md](DEEPER-RETURN-PERIODS.md): the first 15 digits of the reduced stack reach a witnessed period of 25,600 Y blocks after a 25-Y-block preperiod witness. A separate finite root replay now uses the second positional moment to reconstruct the first three-digit terminal tail exactly and confine the second four-digit terminal quotient to [283,510,228, 296,203,294], excluding powers of two at that event; this is a finite-state certificate, not an all-time invariant (see [ROOT-EXTENSION-1310720.md](ROOT-EXTENSION-1310720.md)).

Run the deterministic reproduction with:

```sh
node s4_nested_depth6.mjs
```

The first 18-prefix scan uses JavaScript `Number` only while the complete prefix mass is bounded below (2^{53}), with that bound asserted at every 327,680-return block. Every later prefix transition, full-stack gate, offset, and accumulated sum uses `BigInt`. The script now also reconstructs Z and F and performs a 1,280-block full-suffix F scan.

## Six pure-word hierarchy

Each row records the effective gate word (C=(c_0,\ldots,c_{g-1})) extracted after the stated prefix cycle. The exact identity is
[
\sum_i c_i+2g=1024N,
]
where (N) is the number of reduced P-returns represented by the word.

| Word | Prefix cycle used | Blocks of previous word | Gates | Head additions | Offset sum | Reduced returns |
|---|---:|---:|---:|---:|---:|---:|
| Q | 18 digits | 64 blocks of 327,680 P-returns | 386 | 402 | 21,474,835,708 | 20,971,520 |
| R | 10 digits | 12,800 Q-blocks | 4,603 | 4,597 | 274,877,906,934,794 | 268,435,456,000 |
| V | 7 digits | 800 R-blocks | 28,802 | 28,830 | 219,902,325,555,142,396 | 214,748,364,800,000 |
| W | 8 digits | 64 V-blocks | 7,278 | 7,149 | 14,073,748,835,532,785,444 | 13,743,895,347,200,000 |
| X | 7 digits | 640 W-blocks | 36,457 | 36,489 | 9,007,199,254,740,991,927,086 | 8,796,093,022,208,000,000 |
| Y | 8 digits | 128 X-blocks | 18,084 | 18,096 | 1,152,921,504,606,846,975,963,832 | 1,125,899,906,842,624,000,000 |

The first three rows reproduce the earlier reductions; W, X, and Y are the subsequent exact extractions.

## Deeper Y/Z/F return maps

Let
[
N_Y=1,125,899,906,842,624,000,000
]
be the number of reduced P-returns represented by one Y block.

- The ninth digit has period 5 under Y. Extracting (Z=Y^5) gives a pure 45,157-gate word with offset sum 5,764,607,523,034,234,879,909,686, representing (5N_Y) returns.
- The tenth digit has period 4 under Z. Extracting (Z^4) gives a skewed map (F=B_{p_F}\circ G_{w_F}), where (|w_F|=90,309), (p_F=73,515,085,360,333,450,329), and the offset sum is 23,058,356,577,051,579,186,369,053. It represents (20N_Y) returns.

The pending-aware identity for F is exact:
[
\sum_i (w_F)_i+2|w_F|+p_F
=1024(20N_Y)
=23,058,430,092,136,939,520,000,000.
]

Starting after one F application, the first 1–5 digits of the suffix after the tenth digit have exact prefix periods:

| Suffix digits tracked (full-stack positions) | Period under F |
|---:|---:|
| 1 (11th) | 4 |
| 2 (11th–12th) | 16 |
| 3 (11th–13th) | 64 |
| 4 (11th–14th) | 320 |
| 5 (11th–15th) | 1,280 |

Each listed period has preperiod zero from that post-F state. The scan applies the full skewed word to the full suffix, not a truncated prefix simulator. It finds no halt in 1,280 F blocks. The stack length grows from 23 to 28 at F block 12, so the full state is not claimed to be periodic.

Since one F block is (Z^4=Y^{20}), the first-15-digit projection reaches the observed cycle after 25 additional Y blocks from the state after the first Y block (one-based Y block 26), and has a witnessed period of 25,600 Y blocks. In reduced P-return units these are:
- preperiod witness: 28,147,497,671,065,600,000,000;
- period witness: 28,823,037,615,171,174,400,000,000.

The period sequence is consistent with a mixed-radix odometer, with powers of four followed by a factor of five. This is a structural hypothesis, not an all-depth theorem. See [DEEPER-RETURN-PERIODS.md](DEEPER-RETURN-PERIODS.md) for the digit cycles, cycle-start suffix, factorization checks, and qualifications.

## Earlier prefix cycles

The exact-integer reproduction also finds:

- Under V, the first eight digits of the suffix after 35 digits have preperiod 1 and period 64.
- Under W, the first seven digits of the suffix after 43 digits have preperiod 1 and period 640.
- Under X, the first eight digits of the suffix after 50 digits have preperiod 1 and period 128.

The 30-digit Y-prefix scan after 10,001 Y blocks still finds no cycle. This is consistent with the new 25,600-Y-block period for the first 15 digits; the 30-digit period may be longer.

## Evidence boundary

The starting 18-digit prefix and `blockRootTail` are connected to the source-certified return-5457 state by the exact BigInt replay in [ROOT-EXTENSION-1310720.md](ROOT-EXTENSION-1310720.md): four 327,680-return blocks (1,310,720 reduced P-returns) reach the complete 24-digit `blockRoot()` stack. Only two full-suffix events occur in that segment; their terminal quotients have odd parts 822,257 and 141,780,809, so both succeed by the source power-gate criterion. This closes the prior computational start-state gap, not the Lean-proof gap.

The generic boundary decomposition is supported by `S4BoundaryWord.lean` and `S4SuffixBoundary.lean`. The concrete Y/Z/F word extractions and prefix periods are exact BigInt computations, but their specific finite certificates are not yet Lean-kernel checked. In particular:

1. The 1,310,720-return bridge is an exact reduced-map replay, not a Lean theorem for the source transitions or their primitive TM step count.
2. The 18-prefix period and later nested cycles still need kernel-checked certificates.
3. The first-15-digit period is a projection result; the suffix beyond digit 15 continues to evolve.
4. No proof that every future gate succeeds, no S4 nonhalting proof, and no BB(6) upper-bound improvement is established.

The mass identities are exact arithmetic checks on extracted words; they are consistency checks, not substitutes for the missing source and all-time proofs.

## Useful existing context

- `../agent5-s4-prefix-causal/s4_suffix_macro.cpp`: first-level 18-prefix macro.
- `../agent5-s4-prefix-causal/s4_nested_macro.cpp`: second-level 10-prefix macro.
- `../agent5-s4-prefix-causal/s4_third_macro.cpp`: third-level 7-prefix macro.
- `../agent5-s4-prefix-causal/TENTH-ATTRACTOR.md`: earlier tenth-coordinate contraction analysis.
- `../agent5-s4-prefix-causal/README.md`: source and prefix-causality context.

## Terminal-quotient obstruction: the mod-31 / length-5 proposal fails

The exact source criterion is `G c S = none iff Pow2(W(S)+c)`, with (W([])=0) and (W(b::S)=b+1+2W(S)); see `S4Octet.G_none_iff_power` and its source check in CI 42543510207. At a full-suffix carry through an n-digit suffix, the terminal empty-tail quotient is (q=(W(S)+c)/2^{n-1}); the gate halts exactly when q is a power of two. Modulo 31, powers of two lie in ({1,2,4,8,16}).

The exact-integer test in `s4_nested_depth6.mjs` rejects the proposed state summary ((W(S)\bmod31,\;\mathrm{length}\bmod5)) in two independent ways:

- The modeled eight-digit R-section tail has (W=57570541714408), (W\bmod31=27), and length 8. The first R offset is (305419363311). The synthetic eight-digit suffix ([1267650600228229401191283841810,0,0,0,0,0,0,0]) has the same two summary values, but (W+c=2^{100}), so its first R gate halts by the source criterion. This is a synthetic counterexample to the abstraction, not a halt on the genuine root.
- The distinct inputs ([0,16]) and ([1,0]) both have ((W\bmod31,\mathrm{length}\bmod5)=(4,2)), and both survive the full 4,603-gate R word, but their output lengths are 12 and 13. Thus R does not induce a deterministic transition on this quotient.

The modeled section tail and R word remain conditional on the numeric prefix-cycle/5457 bridge. The source gate iff is formal; the counterexamples are exact BigInt computations. Full details and qualifications are in [TERMINAL-QUOTIENT-OBSTRUCTION.md](TERMINAL-QUOTIENT-OBSTRUCTION.md).

## Highest-value next work

1. Derive a root-propagated interval for the first and second positional moments through the Q/R/V/W/X/Y/Z/F return words; the new four-digit moment fibre is useful only once its moment inputs are bounded along the genuine root.
2. Prove the 18-prefix cycle and Q-word extraction in Lean, then formalize the Y/Z/F finite word and prefix-cycle certificates.
3. Connect prefix-period growth to a root-reachable monotone tail-growth or nonhalting invariant; the simple mod-31/length-5 quotient is not viable.
4. Use further finite scans only when they test a new period law or invariant, not merely to increase a scan count.

## Execution status

The deterministic script has been updated to reconstruct Z and F and scan 1,280 full-suffix F blocks. The underlying computation was exercised interactively in the V8 runtime, but the committed script itself has not yet been run by repository CI. Treat the file as a reproducibility artifact pending that run, not as CI-certified output.


## 50,000-block terminal-quotient test

The manual [terminal scan](TERMINAL-SCAN-50000.md) completed 50,000 R blocks (230,150,000 gates), recording 13 full-suffix events and no halt. It **falsifies** the proposed invariant (q_{\rm odd}\equiv2\pmod{21}): only one of the 13 later events has that residue. The observed avoidance of power-of-two residues modulo 127 is only a 13-event finite observation, not an invariant. This result is intermediate computational evidence, conditional on the reduced-word bridge; it is not a source-level or all-time proof.
