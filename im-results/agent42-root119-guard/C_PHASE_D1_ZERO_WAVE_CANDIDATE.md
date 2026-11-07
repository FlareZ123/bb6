# C-phase D1 zero-wave return law

Date: 2026-11-07  
Status: **source-import-verified conditional Lean theorem**, with a ten-million-step raw census checking every observed instance and its 1100 shield.

## Theorem

Let (b=(B,h,t)) be a reached B/0 configuration. Suppose (r\ge2) and

\[
t(h-1-i)=1\quad(0\le i<r),\qquad
t(h-r-1)=0,\qquad
t(h-r-2)=1.
\]

Assume also the left-of-head exclusion `NoLeft4 true true false b`: no interval (x,x+1,x+2,x+3) with (x+3<h) has tape word (1100).

Then the authentic auxiliary transition table has a configuration (b') such that

\[
\operatorname{shuttleRun}(r+7,b)=\operatorname{some}(b'),
\qquad b'.q=B,\quad b'.tape(b'.h)=0,
\qquad b'.h=h-r+1,
\]

and (b') is reached and satisfies `NoLeft4 true true false`. Consequently (b') cannot satisfy `BBad`, since every `BBad` witness contains a left-of-head (1100) factor in tape order.

The exact Lean statement is `BB6Root119.b0_cphase_d1_zero_wave_return` in [Root119CPhaseReturn.lean](Root119CPhaseReturn.lean).

## Transition derivation

The run decomposes into:

1. B/0 writes one at (h) and moves left to C at (h-1).
2. C/1 erases the (r) consecutive ones at (h-1,\ldots,h-r).
3. C/0 at (h-r-1) writes one and moves left to D at (h-r-2).
4. D/1 writes one and moves right to F at (h-r-1).
5. F/1 writes zero and moves right to D at (h-r).
6. D/0 writes zero and moves left to E at (h-r-1).
7. E/0 writes one and moves right to A at (h-r).
8. A/0 writes one and moves right to B at (h-r+1).

The first two parts take (r+1) steps; the six-step C/0-D/1-F/1-D/0-E/0-A/0 tail gives total duration (r+7). The returned head cell is one of the C/1-erased cells because (r\ge2).

## Formal proof structure and verification

[Root119CPhaseReturn.lean](Root119CPhaseReturn.lean) proves:

- `noLeft4_excludes_BBad`: the (1100) exclusion rules out the exact reachable stopping-gate word.
- `scan_from_B_exact`: the B-to-C scan takes exactly (r+1) primitive steps, preserves the prefix at and left of the C head, and records that every scanned one has been erased.
- `cphase_d1_tail`: the six explicit transitions return to B/0 at head (c.h+2), preserving the (1100) exclusion.
- `b0_cphase_d1_zero_wave_return`: composes the scan and tail, yielding exact time (r+7), exact head (h-r+1), reachability, shield preservation, and exclusion of `BBad`.

The shield proof is local and exact. After the scan, all cells at and left of the C head are unchanged. The tail changes only the cells (p-1,p,p+1), where (p) is the C head, and leaves each of those three cells equal to one at the endpoint. The endpoint head is (p+2). A four-cell window ending before that head either ends at (p-1,p,) or (p+1), where its final bit is one, or ends at or before (p-2), where the entire window is unchanged. Thus an excluded (1100) word cannot be introduced. Separately, the final head cell (p+2) remains zero from the scan.

The manual original-source workflow [42412861860](https://github.com/FlareZ123/bb6/actions/runs/42412861860) succeeded on the repository's actual `Root119Gate`, `Root119CGate`, `Root119BRegular`, `Root119BShield`, and `Root119ShuttleSupport` dependency chain. All four theorem axiom reports contain only `propext` and `Quot.sound`; no `sorryAx` appears. The workflow also runs the ten-million-step raw audit described below.

## Ten-million-step evidence

The independently reproducible Node.js audit [test-root119-two-wave-census.cjs](test-root119-two-wave-census.cjs) replays 10,000,000 primitive transitions of the auxiliary blank-root machine. It reports 22,984 B/0 configurations and 22,983 consecutive completed intervals:

| Class | Count |
|---|---:|
| C-phase D1 candidate | 15,198 |
| Existing odd-wave | 7,508 |
| Existing left-one-wave | 177 |
| New even prefix theorem | 21 |
| New odd-even prefix theorem | 22 |
| Unmatched left-prefix candidates | 8 |
| Other | 49 |
| **Total** | **22,983** |

The C-phase candidate run-length histogram is:

- (r=2): 1 interval;
- (r=3): 15,176 intervals;
- (r=4): 21 intervals.

The audit now checks both shield premises and shield endpoints for every observed C-phase D1 return:

| Audit | Count |
|---|---:|
| C-phase D1 inputs satisfying (1100) exclusion | 15,198 |
| C-phase D1 outputs satisfying (1100) exclusion | 15,198 |

It also checks exact return time and head for every candidate. The raw run and audit are finite computational evidence; they do not establish that every future blank-root B/0 state has these conditions.

## Remaining mathematical obligation

This theorem resolves the C-phase D1 conditional return family and its shield transport. It does not prove that the authentic blank-root orbit remains shielded for all time, nor that every future B/0 interval belongs to one of the existing conditional macro families. The eight unmatched left-prefix candidates and 49 other intervals remain outside this classification. The 43 even/odd-even prefix laws also still need shield transport integrated into a global invariant.

Next work should combine the C-phase result with the existing odd-wave and left-one-wave shield-preserving laws, prove the corresponding conditions for the 43 prefix cases, and investigate the 57 residual intervals. No exact BB(6) value, universal upper bound, or all-time blank-root decision follows from this conditional theorem.
