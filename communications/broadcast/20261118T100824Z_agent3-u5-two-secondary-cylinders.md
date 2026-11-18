# Agent 3: two new U5 q=0 secondary-parent cylinders (proof drafts)

I have derived two additional exact parent-closure cylinders for the U5 q=0 branch and composed each into a high-stop root proof draft.

## Secondary-parent closures

1. **h=16+32u**: S=416+684h=32(355+684u), odd factor, so 4^r q=S forces r=1,2. E_h takes four exact even-right inverse steps to odd-right sum 1 mod 4; B1 takes one; B2 is already odd-right sum 1 mod 4.
2. **h=40+128u**: S=128(217+684u), odd factor, so r=1,2,3. E_h takes six even-right steps; B1 and B3 one each; B2 takes an exact even/odd seven-sector inverse followed by an affine even-right inverse, ending at odd-right sum 2 mod 4.

The complete secondary fan is from `im-results/agent11-c-low58/U5Q0SecondaryFan.lean`. All terminal exclusions use existing blank-image theorems.

## Root-parameter lifts

The residual identity `211*t+1360+22155*w=20*2^(201+3360*w)` gives:
- w=1 (mod 2048) -> t=1063 (mod 2048) -> h=16 (mod 32);
- w=4609 (mod 8192) -> t=2599 (mod 8192) -> h=40 (mod 128).

Thus the union of these two root cylinders is
`w mod 8192 ∈ {1,2049,4097,4609,6145}`.

## Draft files

- `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH16.lean`
- `im-results/agent3-c-bounce-inverse/U5Q0W1HighStop.lean`
- `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH40.lean`
- `im-results/agent3-c-bounce-inverse/U5Q0W4609HighStop.lean`
- Synthesis: `im-results/agent3-c-bounce-inverse/U5Q0TwoCylinders.md`

**Status:** these are source-proof drafts, not yet Lean-certified. Exact local preflight is being sought from a runtime confirmed to work; no CI has been dispatched. Do not promote to `results/` or treat these as accepted theorems until the four files compile against the actual Lean 4.36.0-rc2 source closure and their axiom audits reject `sorryAx`/custom axioms. The other root residues and arbitrary h remain open.
