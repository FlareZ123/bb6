# M0 even, n = 8k+4: 51-step q4 bridge candidate

**Status: deterministic simulation candidate only; not yet Lean-checked or source-composed.** This is the next row after the proposed M1 odd (n=8q+5) row in the root countdown: marker (m=0), index (n=8k+4), target marker (m=2), index (8k+3).

## Finite bridge found

After the (3a)-cell counted left sweep from
[
S1(L,8k+4,0,a,0,b,h),
]
the local machine configuration is state 3 at the new head. For the base (L=3,k=0,a=1,b=0), direct simulation of the original TM2 table gives the following finite bridge (coordinates relative to the post-sweep head):

```lean
def m0EvenFourBridgeStart : FConfig :=
  ⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3]⟩

def m0EvenFourBridgeEnd : FConfig :=
  ⟨4, 3, [-12,-11,-10,-7,-4,-1,1,2,3]⟩

-- candidate kernel certificate:
theorem m0EvenFourBridge_exact :
    fRun tm2 51 m0EvenFourBridgeStart =
      some m0EvenFourBridgeEnd := by decide
```

The simulated head range is exactly ([-12,3]), so `Finset.Icc (-12) 3` is a sufficient frame window. The bridge only reads/writes in that window. The start pattern in it is determined by
`markerWord0 ++ d0 ++ binDec 3 4`; in particular
`binDec 3 4 = d1 ++ d1 ++ d0`. The high tail `binDec (L-3) k ++ lh` begins strictly left of the frame and is not read by this bridge. The right unary counter is also outside the read window and is preserved.

At the end, the state-4 head is at offset (+3). The preserved right tape and the finite end pattern have the q4 suffix shape
[
1^5,00,1^{3(b+1)},0^5
]
at that head. The 51-step bridge displacement is (+3).

## Count and expected composition

The left sweep costs (9a). The bridge costs 51. The state-4 E-scan from offset (3) back to the original head costs (3a-3). Thus the prefix before the generic q4 suffix has candidate cost
[
9a+51+(3a-3)=12a+48.
]
The generic q4 suffix costs (39+3b), giving the full reset-prefix candidate
[
12a+87+3b.
]
This agrees with the proposed `proposedIncrementCost 0 (8*k+4) a b` after subtracting the all-ones drain cost, since (v_2(8k+4)) is not uniformly 2 for arbitrary k. **For the root subfamily (n=16r+4), (v_2(n)) may exceed 2 when r is odd/even in certain cases; the formula above is therefore only the (k=0) low-bit bridge cost until the full residue/valuation conditions are established.** Do not promote the cost identity without the required (v_2(n)) side conditions.

The remaining mathematical work is to prove the general input-frame match for (n=8k+4), prove the left-facing output/tail identity needed by `q4_suffix_run_to_s1Config`, and verify the exact 51-step bridge and head bound in Lean. Then compose the generic q4 suffix and counted drain. No `Rst0` theorem is claimed yet.

## Reproduction

The simulation used the original `tm2` transition table from `BB6Coverage.ChampionRootBridge`, with `s1Config L 4 0 1 0 0 0`, the source `binDec`/marker words, and three successive `holeThree` left-sweep moves. The finite run is deterministic; the Lean `fRun` certificate above is the intended independent kernel check.

```javascript
const tm2 = [
  [[true,true,1], null],
  [[true,false,2], [false,true,5]],
  [[true,true,4], [false,false,3]],
  [[false,false,2], [true,true,1]],
  [[true,true,0], [true,true,4]],
  [[true,true,4], [false,true,3]]
];
// true means tape bit 1; the two entries are read-0 and read-1.
// Start after the 3-cell left sweep with marked positions
// [-10,-9,-8,-7,-6,-5,-4,-1,2,3] and state 3/head 0.
let tape = new Set([-10,-9,-8,-7,-6,-5,-4,-1,2,3]);
let state = 3, head = 0, min = 0, max = 0;
for (let step = 0; step < 51; step++) {
  const [write, right, next] = tm2[state][tape.has(head) ? 1 : 0];
  if (write) tape.add(head); else tape.delete(head);
  head += right ? 1 : -1;
  state = next; min = Math.min(min, head); max = Math.max(max, head);
}
const end = [...tape].sort((a,b)=>a-b);
({state, head, min, max, end});
```

The code block is a compact bridge-only reproduction; the source tape outside the finite window must still be supplied by the S1 encoding when lifting with `frameAt`.
