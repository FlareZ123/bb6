# S4 tenth-coordinate attractor over the nine-prefix cycle

**Mathematical scope, 9 November 2026.** This is an intermediate theorem about the total, length-preserving S4 prefix projection, with a conditional consequence for the actual blank-root trajectory of the six-state machine \`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF\`. The global halting/nonhalting question for S4, and BB(6), remains open.

The exact numerical data and a finite arithmetic witness are in [tenth_carry_attractor.py](tenth_carry_attractor.py). The previously original-source-checked [all-depth prefix causality](README.md) and [authentic root through 5,457 returns](S4PrefixNinthBase.lean) provide the source interface. The nine-digit total prefix period has complete source-compiling block certificates; its final composition [S4PrefixNinthCycle.lean](S4PrefixNinthCycle.lean) is being checked separately.

## All-input tenth-coordinate theorem

Let

\`\`\`
p = (283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050)
\`\`\`

and let \`pp\` be the length-preserving total prefix projection of the original S4 return \`P=G(509);G(290);G(219)\`. The exact arithmetic identity \`pp^81920(p)=p\` allows defining \`F : Nat -> Nat\` by

\`\`\`
pp^81920(p ++ [v]) = p ++ [F(v)].
\`\`\`

For **every** natural number \`v\`,

\`\`\`
floor(v / 2^703) + 366445 <= F(v) <= floor(v / 2^703) + 366450.
\`\`\`

Exactly **703** of the 245,760 constituent \`G\` operations over the nine-prefix cycle perform a full odd-carry scan across all nine digits and hence halve the tenth-coordinate contribution. Each of the remaining stages updates that coordinate additively or leaves it unchanged. The bound incorporates all 245,760 stages, including their exact additive offsets.

The exact six-value transition table is:

| v | F(v) |
| --- | --- |
| 366445 | 366447 |
| 366446 | 366449 |
| 366447 | 366446 |
| 366448 | 366448 |
| 366449 | 366445 |
| 366450 | 366447 |

Consequently, **every initial natural tenth digit** eventually enters one of two terminal components under the total prefix block map: a fixed point at \`366448\`, or the four-cycle

\`\`\`
366445 -> 366447 -> 366446 -> 366449 -> 366445.
\`\`\`

The existence of the separate fixed point is an obstruction to claiming universal synchronization to the root's four-cycle.

The previously source-certified full S4 stack at reduced return 5,457 has tenth digit \`366446\`. Thus, **conditional on continued genuine S4 survival**, at times \`5457 + 81920*m\` this digit follows the four-cycle while the first nine digits return to \`p\`. The first ten digits therefore return to their original values after \`327680\` reduced returns along any surviving root history. This does not assert that the complete stack repeats or that the machine survives to any future stopping candidate.

## Proof mechanism

For a nine-digit prefix \`q\` and gate offset \`c\`, initialize \`a=q[0]+c\`. If the active carry \`a\` is odd at position \`i\`, emit \`floor(a/2)\` and advance with \`a = q[i+1] + floor(a/2) + 1\`. If it is even, emit \`a/2+2\`, update the next digit by \`+a/2\`, and stop the scan. This is a direct expansion of the established total \`hp/gp\` recurrence. An induction on the nine positions proves that the nine output digits are independent of the appended tenth digit. That tenth digit undergoes precisely one of

\`\`\`
v -> v+d
v -> f(v+d),   f(z) = z//2 + 2 if z is even, else z//2,
\`\`\`

where \`d\` is a nonnegative integer determined solely by the nine-digit prefix and \`c\`. In a terminating-even carry at the ninth position, \`d=a/2\`; when the carry stops earlier, \`d=0\`; when all nine positions have odd carries, \`d=a/2+1\`.

The all-odd carry condition is equivalent to \`(W(q)+c) % 512 == 0\`, where \`W(q)=sum((q[i]+1)*2^i, i=0..8)\`. This follows by iterating the binary weighted-tail identity under odd carry; at each scan the low bit vanishes and the next carry is exactly the shifted weighted tail. It gives an independent congruence check on every one of the 703 half-drains and connects them to the existing 703 potential stopping-gate phases. Congruence alone gives no genuine-root halting witness.

Maintain a universal envelope for the scalar map at each stage:

\`\`\`
floor(v / 2^r) + lo <= current(v) <= floor(v / 2^r) + hi.
\`\`\`

Initially \`(r,lo,hi)=(0,0,0)\`. For a step \`+d\`, update \`lo += d\` and \`hi += d\`. For a half-drain, use \`floor(z/2) <= f(z) <= floor(z/2)+2\` and the monotonicity of integer division to update

\`\`\`
r  <- r+1
lo <- floor((lo+d)/2)
hi <- ceil((hi+d)/2)+2.
\`\`\`

The envelope inequalities follow by induction for every input \`v\`. The exact-integer checker exhausts the finite 81,920-return sequence and obtains \`(r,lo,hi)=(703,366445,366450)\`, simultaneously checking that the nine-digit prefix has returned to \`p\`. It separately tests the scalar transfer against the genuine ten-coordinate total \`gp\` recurrence and evaluates all six exact boundary transitions.

Put \`B=2^703\`. When \`v>=B\`, the upper bound gives \`F(v) <= floor(v/B)+366450 < v\`, so a strictly descending chain must reach some \`v<B\`. From there, the next image lies in \`[366445,366450]\`, and the six-entry table proves that all subsequent values enter one of the two terminal components. This completes the global attractor argument for the total prefix map.

## Evidence boundary and next decisive problem

The scalar recurrence and universal bound are mathematical deductions with an explicit finite 245,760-stage certificate, independently executable with Python's exact integers. The numerical \`703\`, envelope endpoints and six transitions are asserted in the committed checker. Their **full numerical evaluation is not yet a Lean-kernel theorem**. The nine-prefix total cycle is itself a finite, separately source-imported Lean calculation whose formal-composition status should be taken from the current CI result.

An all-time original-source correspondence from the total prefix dynamics requires the established hypothesis that the authentic \`P\` trajectory survives. The present theorem restricts a genuine root's prefix conditional on survival. It cannot exclude the remaining full-stack binary-power halting gates; synthetic suffixes with the same short prefix and even the same mass can still halt. Closing the **true evolving suffix** at those 703 possible gates, or finding an actual halt, remains the substantial open problem.