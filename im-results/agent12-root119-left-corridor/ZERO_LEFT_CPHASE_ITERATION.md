# Root119 zero-left even-run: full C-phase sweep-back

**Status:** the mathematical composition is derived from the existing exact source-machine return lemmas. The companion Lean file, Root119ZeroLeftFullReturn.lean, is a formalization draft; it still requires the manual original-source CI compile. This is an intermediate result, not a global classification theorem.

## The new finite-parameter return

Let \(b=(B,h,t)\) be a genuinely reached B/0 configuration. Assume:

- \(t(h)=t(h-1)=t(h-2)=t(h-3)=0\);
- \(t(h+1),\ldots,t(h+2n)=1\);
- \(t(h+2n+1)=t(h+2n+2)=0\);
- the left-of-head forbidden-word shield \(\operatorname{NoLeft4}(b)\): no four consecutive cells strictly left of the head contain \(1100\).

Then the literal auxiliary #119 machine returns to B/0 at the **same head coordinate** after exactly

\[
(2n+12)+10(n+1)=12n+22
\]

primitive steps. If the endpoint is \(b'=(B,h,t')\), it has:

\[
\begin{aligned}
&t'(h-3)=t'(h-2)=t'(h-1)=1,\qquad t'(h)=0,\\
&t'(h+1+2j)=0,\quad t'(h+2+2j)=1
       &&(0\le j\le n),\\
&t'(x)=t(x) &&(x\le h-4),\\
&t'(x)=t(x) &&(x\ge h+2n+3),\\
&\operatorname{NoLeft4}(b').
\end{aligned}
\]

In words, the corridor

\[
000\ \big|\ 1^{2n}00
\]

is converted, at the same B/0 head, into

\[
111\ \big|\ (01)^{n+1},
\]

with both exterior half-lines unchanged and the 1100 shield preserved. The displayed right-hand word is written from the head's right neighbor toward increasing tape coordinates.

This is a **composition/refinement** of the already established right-gateway family, not a new independent input family. It does, however, close the whole right-gateway corridor into a same-head normal form rather than stopping at the first rightward B/0 return.

## Why the extra n+1 C-phase returns exist

The existing exact zeroLeftEvenRun_exact theorem gives, after \(2n+12\) steps, a B/0 at

\[
H=h+2n+2.
\]

Its left boundary has the local word \(11101\) at \(H-1,\ldots,H-5\). More generally, the output has the alternating corridor

\[
t_{\rm sweep}(H-4-2j)=0,\qquad
t_{\rm sweep}(H-5-2j)=1
\quad (0\le j\le n).
\]

The first pair is precisely the C-phase D1 entry condition for a three-cell scan. Each pair farther left is the next entry condition after the previous return.

The source theorem b0_cphase_d1_zero_wave_return with scan length \(r=3\) gives a ten-step B/0-to-B/0 return. Its head moves from \(H\) to \(H-2\); it writes the six-cell local word

\[
t_{\rm out}(H-5,\ldots,H)=111001
\]

and preserves the tape at every \(x\le H-6\). The exact step also preserves every \(x\ge H+1\). The output has three ones immediately to the left of its new head, and the next untouched left pair is the old pair at \(H-6,H-7\). Therefore the same \(r=3\) theorem applies again.

Inductively, the \(j\)-th return consumes the pair at the current head minus four and minus five, moves the head left by two, and writes a new 01 pair immediately to its right. After \(n+1\) returns, all \(n+1\) alternating pairs have been consumed and the head is back at \(h\). The written pairs are now the right-hand \((01)^{n+1}\) corridor in the displayed endpoint.

The shield is transported at every C-phase return by the existing source theorem. The tape-exterior bounds compose: each step preserves \(x\le H-6\) and \(x\ge H+1\), so after the full sweep-back the original left exterior \(x\le h-4\) and right exterior \(x\ge h+2n+3\) are untouched.

## Research significance and limitation

This resolves the *internal continuation* of every zero-left even-run input satisfying the stated shield: the first rightward B/0 return is not the end of the physical macro. The complete macro comes back to the original head and exposes a canonical \(111\mid(01)^{n+1}\) local shape. It gives a useful normalized node for a future B/0 macro graph and avoids treating the \(n+1\) C-phase returns as separate census events.

It does **not** establish that every genuinely reached B/0 configuration belongs to this family, nor that the new normal form's next return is globally determined. In particular, it does not close the dangerous odd-even boundary or prove the all-time NoLeft4 invariant. The result is conditional on the input corridor and shield.

## Formalization

Root119ZeroLeftFullReturn.lean contains:

1. an exact tape refinement of the ten-step \(r=3\) C-phase D1 return;
2. the alternating-pair corridor lemma for zeroLeftEvenOutTape;
3. an induction for \(m\) repeated C-phase returns;
4. the composed zeroLeftEven_full_return theorem with time \(12n+22\), same-head endpoint, two-sided exterior agreement, alternating right corridor, and shield.

The new file is included in the manual original-source workflow agent42-root119-zero-left-even-run.yml. A successful run is still required before calling the Lean formalization source-verified. No claim about BB(6)'s exact value follows from this conditional macro.
