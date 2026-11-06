# Additional Sheep power-gate parent families at valuations three, six and seven

**Scientific status.** Exact all-parameter mathematical constructions for three legal first-even return source families, with modular and legal-source arithmetic independently certified by standalone Lean 4.36.0-rc2 files. These certificates supplement a published one-variable model already linked to the original six-state Turing machine by Agent16. The complete combined all-`k` counting statement, its 3-adic prerequisites, and an original-source E-edge composition have conventional proofs below; they are **not** yet a single unchanged-source Lean theorem. The resulting parents are synthetic: their membership in the authentic blank-tape orbit is **unknown**. This supplies no Sheep decision, no Busy Beaver upper bound, and no exact BB(6) value. External novelty is unassessed. This dossier belongs in `im-results/`.

The Sheep machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its legal nonterminal generic section return from even `x=2^a*v`, `a>=1`, odd `v>=5`, is

\[
F(x)=2^a v+a+(v-1)/2.
\]

Writing `F(x)-1=2^h q` with `q` odd, the exact first-even section return is `E(x)=1+3^h q`. See Agent16's [original-machine semantic verification](../agent16-sheep-even-return/README.md), [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), for the source-to-E bridge.

## Main constructive theorem

For every integer `k>=1`, set

\[
j=2\cdot3^k,\qquad Y_k=2^j,\qquad H=k+1,\qquad
q_h=(2^j-1)/3^h\quad(1\le h\le H).
\]

For any source valuation `a` in the table, define

\[
v_{a,h}=\frac{2^{h+1}q_h-(2a-3)}{2^{a+1}+1},
\qquad x_{a,h}=2^a v_{a,h}.
\]

Every listed `(a,h)` gives an integer `v_{a,h}>=5` that is odd, and a **genuine legal first-even return edge** `E(x_(a,h))=Y_k` with exactly `h` hidden odd steps.

| Source valuation | Chosen lengths `h` | Proven status |
|---|---|---|
| `a=1` | all odd `1<=h<=k+1` | Previously proved by Agent17 in [UNBOUNDED-POWER-FANIN.md](../agent17-sheep-geometric-rays/UNBOUNDED-POWER-FANIN.md) |
| **`a=3`** | `1<=h<=k+1` and `h%16=10` if `k` even, or `h%16=14` if `k` odd | New complete **iff** for positive hidden length at this source valuation; [Lean certificate](SheepA3Boost.lean) |
| **`a=6`** | `6|k`, `1<=h<=k-1`, and `h%21=20` | New guaranteed infinite family, not asserted exhaustive; [Lean certificate](SheepA6Boost.lean) |
| **`a=7`** | `1<=h<=k+1` and `h%256=221` if `k` even, or `h%256=83` if `k` odd | New guaranteed infinite family, not asserted exhaustive; [Lean certificate](SheepA7Boost.lean) |

The `a=3` iff applies to every generic even source `x=8v`, `v>=5` odd, whose E return is this power target. The remaining `h=0` case cannot occur with `a=3` by the prior [uniform valuation theorem](../agent17-sheep-geometric-rays/UNIFORM-VALUATION.md). The special cofactor-three source `x=24` has `E(24)=30` and is excluded. The `a=6` and `a=7` rows are sufficient constructions with no claim to classify all legal predecessors at those valuations.

All displayed sources have distinct 2-adic valuations across rows. Within a row they are distinct since `2^(h+1)*q_h=2*(2/3)^h*(2^j-1)` strictly decreases with `h`.

### Quantified consequence for direct indegree

Let `A3(k)` count the chosen valuation-three lengths:

\[
A_3(k)=
\begin{cases}
0,& k\ \mathrm{even},\ k<10,\\
1+\lfloor(k-10)/16\rfloor,& k\ \mathrm{even},\ k\ge10,\\
0,& k\ \mathrm{odd},\ k<13,\\
1+\lfloor(k-13)/16\rfloor,& k\ \mathrm{odd},\ k\ge13.
\end{cases}
\]

Let `A7(k)` be the number of integers `h` in `[1,k+1]` satisfying the valuation-seven row. Let `I(k)` be one if `6|k` and zero otherwise. All these counts are constructive, so

\[
\operatorname{indegree}_E(Y_k)
\ge
\left\lceil\frac{k+1}{2}\right\rceil
+A_3(k)+A_7(k)+I(k)\left\lfloor\frac{k}{21}\right\rfloor.
\]

For large `k`, `A3(k)=k/16+O(1)` and `A7(k)=k/256+O(1)`; for `k` divisible by six the constructed valuation-six count equals `floor(k/21)`. Consequently

\[
\liminf_{k\to\infty}
\frac{\operatorname{indegree}_E(2^{2\cdot3^k})}{k}
\ge \frac{145}{256}=0.56640625,
\]

\[
\limsup_{k\to\infty}
\frac{\operatorname{indegree}_E(2^{2\cdot3^k})}{k}
\ge \frac{3301}{5376}\approx0.614025297619.
\]

These bounds strengthen the previously exhibited slope `1/2` along the same power-gate sequence. They are lower bounds on the **synthetic graph's legal direct-parent count**. Other source valuations can contribute more parents. None of these parents is proved reachable from section entry `10`.

## All-exponent proof

**3-adic valuation and legality.** The exact order formula `v3(2^(2*3^k)-1)=k+1` follows inductively from `U^3-1=(U-1)(U^2+U+1)` with `U=4^(3^k)=1+3s` and `U^2+U+1=3*(1+3s+3s^2)`. Thus all `q_h` above are positive, odd integers. Their least possible size occurs at `h=k+1`; `q_(k+1)>=7` holds at `k=1` (equality) and persists because the exact quotient multiplies by `(U^2+U+1)/3>=1` at each increment of `k`.

For a generic `a`, direct substitution into `F` gives

\[
2(F(2^a v)-1)=(2^{a+1}+1)v+(2a-3).
\]

Therefore `E(2^a v)=Y_k` with hidden length `h` is equivalent to the displayed `v_(a,h)` being an odd integer at least five. Once integral, oddness follows because the numerator `2^(h+1)*q_h-(2a-3)` and denominator `2^(a+1)+1` are both odd. The explicit residue classes all have `h>=10` except the previously treated `a=1` family; with `q_h>=7` this ensures `v>=5`. Because `q_h` is odd, the reconstructed hidden valuation is exactly `h`.

**Valuation three, complete classification.** The congruence required for `v` to be integral is `2^(h+1)*q_h=3 (mod17)`. Since `3^h*q_h=2^j-1`, this is equivalent to

\[
3^{h+1}\equiv 2^{h+1}(2^j-1)\pmod{17}.
\]

For even `k=2s`, `2^j=4^(9^s)=4 (mod17)`; for odd `k=2s+1`, `2^j=4^(3*9^s)=13 (mod17)`. Both 2 and 3 have period 16 modulo 17. Exact inspection of one full 16-term period gives the unique solutions `h%16=10` and `h%16=14`, respectively. The all-natural iff and legal-source equations are kernel-certified by [SheepA3Boost.lean](SheepA3Boost.lean). They establish both necessity and sufficiency for this fixed source valuation.

**Valuation six, subsequence `6|k`.** Here `2^(a+1)+1=129=3*43`, and `2a-3=9`. For `k=6m`, `2^j=4 (mod43)`, using `4^7=1 mod43` and `3^6=1 mod7`. Choose `h=21t+20`, giving `h+1=21(t+1)` and

\[
2^{h+1}\equiv3^{h+1}\pmod{43},
\]

because `2^21=3^21=-1 mod43`. It follows that

\[
2^{h+1}q_h
\equiv3^{h+1}q_h
=3(2^j-1)\equiv9\pmod{43}.
\]

The condition `h<=k-1` forces `3^2|q_h`, so `2^(h+1)q_h-9` is also divisible by three. Coprimality of 3 and 43 makes this numerator divisible by 129, yielding the claimed odd cofactor `v=(2^(h+1)q_h-9)/129`. All-modulus congruence, parity and size are checked in [SheepA6Boost.lean](SheepA6Boost.lean). The allowed `h` are exactly `20,41,62,...<=k-1`, giving `floor(k/21)` distinct constructed parents whenever `6|k`.

**Valuation seven, uniform extra family.** Here `2^(a+1)+1=257` and `2a-3=11`. Since `4^9=4 (mod257)`, one has `2^j=4 (mod257)` for even `k` and `2^j=64 (mod257)` for odd `k`. Both 2 and 3 satisfy `z^256=1 mod257`. For `h=221+256t`, their residues are `3^h=76`, `2^(h+1)=193 (mod257)`; the equation `3^h q_h=2^j-1` forces `q_h=44 (mod257)` and `193*44=11 (mod257)`. For `h=83+256t`, the corresponding residues are `115`, `16`, `q_h=81`, and `16*81=11 (mod257)`. Thus `v=(2^(h+1)q_h-11)/257` is an odd integer at least five in both cases. The complete all-exponent arithmetic, including finite residue certificates over all 257 residues, is checked in [SheepA7Boost.lean](SheepA7Boost.lean). The two selected progressions each contribute asymptotically `k/256` legal parents, regardless of the parity of `k`.

## Verification, provenance and remaining obstacle

Three exact, readable standalone Lean files, each with `import Std`, were locally compiled under **Lean 4.36.0-rc2**:

- [SheepA3Boost.lean](SheepA3Boost.lean): `mod_iff_even`, `mod_iff_odd`, `parent_even`, `parent_odd`, complete modulo-17 iff, axioms `[propext, Quot.sound]`.
- [SheepA6Boost.lean](SheepA6Boost.lean): `mod43_sufficient`, `parent_arithmetic`, `parent_six`, axioms `[propext, Quot.sound]`.
- [SheepA7Boost.lean](SheepA7Boost.lean): `mod_even`, `mod_odd`, `parent_even`, `parent_odd`, axioms no stronger than `[propext, Quot.sound]`.

None uses `sorry`, `admit`, `sorryAx`, `native_decide`, or user-supplied axioms. Lean certifies the modular and cofactor construction under explicitly stated `3^h q+1=2^j`, size and (for `a=6`) divisibility premises. The elementary induction on `k`, source E semantics, distinctness, and total counting are mathematical proofs stated above, **without a new single combined Lean theorem connected to unmodified source**.

Independent [fanin_boost_verify.py](fanin_boost_verify.py) reproduces **2,362** exact positive modular source cases for `k=1..256` across `a=3,6,7`, including 240 `a=6` and 106 `a=7` cases, plus three fully materialized low-`k` original-F/E transitions. The full-source digest is `d4c0e2af63be390312512e00e6ffd509404176fcdfe80ea267c34bae68246ae9`. The separate [a3_boost_verify.py](a3_boost_verify.py) checks **all** `h=1..k+1` through `k=128`, 8,384 candidate lengths, to supplement the formal valuation-three iff. Large examples rely on modular exponentiation because the true target power has astronomically many bits.

**Prior distinctions:** Earlier [A3-POWER-FANIN.md](../agent17-sheep-geometric-rays/A3-POWER-FANIN.md) studied a different target sequence `j=4*3^k` and `h=1 mod16`. The present `j=2*3^k` family has `j=2 mod4` and `h=10/14 mod16`. The previously established valuation-one family remains credited to its original theorem.

**Decisive unsolved requirement:** Find a history-sensitive, genuine blank-entry invariant excluding every surviving power gate, or exhibit a legitimate blank-origin halting path. The all-modulus synthetic mixing obstructions of Agents 16, 17 and 22 rule out broad classes of residue-only proof approaches. Increasing the synthetic indegree alone does not resolve BB(6).
