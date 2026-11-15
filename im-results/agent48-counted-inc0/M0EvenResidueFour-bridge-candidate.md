# M0-even residue-four source reset: exact bridge and lift contract

**Status: intermediate Lean source draft; not compiled or source-composed.** The target is the next authentic TM63 root transition after Agent 42's middle-row-11 endpoint:
`S1(L,16r+4,0,A,0,B,H) → S1(L,16r+3,2,A+B+1,0,2^B-1,H+5+3B)`,
with residue parameter `k=2r`. This is an Rst0 row, not a machine halt or a BB(6) result.

## 1. Finite 51-step bridge

After the counted `3a`-cell left sweep from `S1(L,8k+4,0,a,0,b,h)`, the post-sweep head is at `h-3a`. The finite bridge is:

```lean
def m0EvenFourInside (x : Int) : Bool :=
  decide (-12 ≤ x ∧ x ≤ 3)

def m0EvenFourBridgeStart : FConfig :=
  ⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3]⟩

def m0EvenFourBridgeEnd : FConfig :=
  ⟨4, 3, [-12,-11,-10,-7,-4,-1,1,2,3]⟩

theorem m0EvenFourBridge_exact :
    fRun tm2 51 m0EvenFourBridgeStart =
      some m0EvenFourBridgeEnd := by decide
```

The source file `M0EvenFourQ4Bridge.lean` now contains this finite certificate, the `List.range 51` head-confinement proposition, both low-three-block binary identities, and the parameterized base-input-frame match. `M0EvenFourQ4Prefix.lean` composes that bridge with the counted left sweep and E-scan, giving the base `L=3,n=4` source run `m0EvenFour_q4_prefix_run` at cost `48+12*a`, together with an intermediate-head lower bound for the half-line frame lift. **Both modules are drafts until compiled; the arbitrary-tail lift and q4 suffix/drain are still missing.**

The low-three-block words are:
- `binDec 3 4 = d1 ++ d1 ++ d0`;
- `binDec 3 3 = d0 ++ d0 ++ d1`.

For `y∈[-12,0]`, the input frame is read from the source suffix
`markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh`; its marked positions in the bridge window are exactly `-10,-9,-8,-7,-6,-5,-4,-1`. The post-sweep cells at offsets `1,2,3` are respectively blank, marked, marked. This is the exact input pattern in `m0EvenFourBridgeStart`.

## 2. The arbitrary-tail identity that makes the lift possible

For every `L≥3` and `8k+4<2^L`, the encoder recurrence gives
```
binDec L (8*k+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) k
binDec L (8*k+3) = d0 ++ d0 ++ d1 ++ binDec (L-3) k
```

Consequently, the source left-facing stream is
```
d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0
  ++ binDec (L-3) k ++ lh
```
and the required M0-even q4-cut stream is
```
[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0
  ++ d0 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh
```

Both words have the same tail beginning at index `3*a+14`; their bit at index `3*a+13` is also true on both sides. The finite bridge window `[-12,3]`, measured from the post-sweep head, reaches precisely through left-facing index `3*a+12`. Thus the higher-order block `binDec (L-3) k` is never read or modified. This is the key half-line frame boundary: use the readable region `x ≥ h-(3*a+12)`, and preserve the complete arbitrary tail strictly to its left.

The bridge output also matches the target prefix locally: after the E-scan of `3*a-3` ones, the left-facing bits are
`[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec 3 3`.
The final bit of this finite pattern is the shared boundary bit above.

## 3. Exact cost and theorem interface

The counted left sweep costs `9*a`; the bridge costs `51`; the E-scan costs `3*a-3`. Therefore the q4-prefix cost is
`9*a + 51 + (3*a-3) = 12*a+48`.

Since `8*k+4 = 4*(2*k+1)`, `v2 (8*k+4)=2`. The repository definition
`resetPrefixCost m n a b = 48 + 12*(a+v2 n) + 15 + 4*m + 3*b`
therefore gives
`resetPrefixCost 0 (8*k+4) a b = 12*a+87+3*b`,
exactly the prefix plus the generic q4 suffix cost `39+3*b`.

The intended full source theorem is:
```lean
theorem m0Even_residue4_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 0 (8*k+4) a b)
      (s1Config L (8*k+4) 0 a 0 b h) =
      some (s1Config L (8*k+3) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b))
```
It still requires the base source-prefix proof, arbitrary-tail frame lift, complete q4 left/right interfaces, M0-specific q4 suffix composition, and counted all-ones drain. No Rst0 source theorem is currently claimed.

## 4. Root integration point

Agent 42's uncompiled `tm63_blank_reaches_after_middle11` ends at
`S1(tm63Length1,16*r+4,0,tm63MiddleAfter11A,0,tm63MiddleAfter11B,tm63MiddleAfter11Head)`.
Substituting `k=2*r` in the theorem above would give the exact next root endpoint
```
S1(tm63Length1,16*r+3,2,
   tm63MiddleAfter11A + tm63MiddleAfter11B + 1,
   0, 2^tm63MiddleAfter11B - 1,
   tm63MiddleAfter11Head + 5 + 3*tm63MiddleAfter11B)
```
and append `proposedIncrementCost 0 (16*r+4) A B` successful transitions. This is a direct continuation of the genuine blank-root run, conditional on the preceding middle-11 source composition and the new source theorem both passing their original-import Lean/axiom gates. Agent 8 has a separate wrapper at `im-results/agent8-root-residue-four/TM63RootResidueFour.lean`; it composes this middle-12 row and the following M2-odd row through middle 13. I removed my duplicate wrapper and will keep the root integration in Agent 8's file.

## 5. Remaining proof work

1. Compile and repair the finite bridge and base-prefix drafts, including the intermediate-head bound; verify their exported declarations have no transitive `sorryAx`.
2. Lift the base run to arbitrary `L,k` using the half-line frame boundary above; prove the complete left-facing stream and the M0-specific q4 right-shape/far-tail conditions.
3. Compile and repair `M0EvenResidueFour.lean`; verify the full q4 suffix/drain composition and its transitive axiom audit.
4. Compile and audit `TM63RootResidueFour.lean` only after the full Rst0 source theorem and the preceding middle-11 dependency are accepted.

The current blocker is source compilation availability: local Python/container execution returned concrete ClientErrors in this invocation and in other active identities' reports. The bridge, base-prefix, arbitrary-tail residue-four, and root-wrapper modules have **not** been compiled. The current root-critical local-compile handoff is with Agent 7; no CI run has been dispatched as a substitute for local source checking. Keep this branch in `im-results/`; do not promote it to `results/` or describe it as a certified root extension.
