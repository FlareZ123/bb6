# F/1-created 1100 marker: targeted 10M census

## Question

The root-119 halting gate is a B/0 configuration with a factor 1100 entirely to the left of the head. The global B/0 NoLeft4 shield is still unproved. This experiment isolates one mechanism by which such a factor can be created behind the head.

## Exact transition table

The replay used the six-state machine encoded as:

`1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`

For each transition, the simulator stores the finite set of 1-cells. After writing at head position h, it recomputes only the four length-4 windows starting at h-3,h-2,h-1,h, since these are exactly the windows whose contents can change.

## 10,000,000-step observations

- Exactly one F/1 transition was observed with left context 110, so that its write-0 created a 1100 factor ending at the old head cell.
- The event is transition 3,194,059, with F/1 head h=-692.
- The rightward maximal 1-run from h+1 has length 405=2·202+1 and is followed by 0.
- The left neighbor h-1 is 0. Thus the pre-transition configuration satisfies the hypotheses of the existing `Root119WaveNormal.wave_explicit` family with n=202.
- That source theorem's 4n+5=813-step return is B/0 at h-1=-693. The newly created 1100 occupies [-695,-692], so its rightmost cell is still to the right of the returned B/0 head; it is not a NoLeft4 violation.
- Across the same 10M replay, no B/0 state had any 1100 factor entirely to its left. Other states do temporarily have such a factor left of the head: the first observed is D at transition 3,194,060, immediately after the F/1 creation. A later B/1 state also has the factor far to its left; this is why the invariant must be B/0-specific rather than a claim that the head never passes 1100.

These are simulator observations, not an all-time theorem. The event census is limited to the first 10M transitions.

## Reproduction code

The following standalone JavaScript uses the transition table above and exact local window updates:

```js
const rules = "1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD".split("_");
const tape = new Set(), limit = 10_000_000, events = [];
let q = 0, h = 0;
const bit = x => tape.has(x);
for (let time = 0; time < limit; time++) {
  const b = Number(bit(h)), r = rules[q].slice(3*b, 3*b+3);
  if (r === "---") break;
  if (q === 5 && b === 1 && bit(h-3) && bit(h-2) && !bit(h-1)) {
    let run = 0;
    while (bit(h+1+run)) run++;
    events.push({transition: time+1, head: h, rightRun: run});
  }
  if (r[0] === "1") tape.add(h); else tape.delete(h);
  h += r[1] === "R" ? 1 : -1;
  q = r.charCodeAt(2)-65;
}
console.log(events);
```

Observed output:

```json
[{"transition":3194059,"head":-692,"rightRun":405}]
```

## Proof direction

This isolates a potentially useful route to the all-time B/0 shield:

1. Classify every reachable F/1/1 state whose three-cell left context is 110.
2. Show that its right corridor belongs to a source-certified return family (the ordinary odd-run wave above, or another exact family).
3. Package the return theorem with the marker geometry: the B/0 endpoint is at or inside the newly created 1100, never strictly to its right.
4. Separately account for 1100 factors created by left-moving zero writes (C/1 and D/0); those are initially to the right of the head.

The main unresolved step is step 1: the single observed odd-run event is not a proof that every future such event has the same shape. The existing 300M corridor evidence and Agent 12's return-family work should be integrated before attempting a broader claim.
