# Sheep: exact direct predecessors for all powers `2^(648t)` with `3∤t`

**New intermediate mathematical theorem, 9 November 2026.** Let `E` be the genuine first-even return map of the six-state Sheep Turing machine
`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. For **every integer `t>=2` with `t%3 != 0`**, the complete set of legal nonterminal even predecessors of `Y=2^(648t)` is described by precisely the following three rows, with **one predecessor per satisfied condition**:

| Necessary and sufficient condition on t | Hidden odd steps h | Source 2-valuation a | Unique incoming source x |
|---|---:|---:|---|
| `t mod 7 = 6` | 3 | 6 | `64*(2^(648t+4)-259)/3483` |
| `t mod 9 = 1` | 5 | 2 | `4*(2^(648t+6)-307)/2187` |
| `t mod 15 = 14` | 5 | 4 | `16*(2^(648t+6)-1279)/8019` |

Every displayed source is an **integer even legal source** with odd cofactor at least five, and its actual first-even return is `Y`. The three sources, when present, are distinct. No other first-even edge into `Y` exists, including exceptional cofactor-three sources. Therefore the exact indegree is

\[
\#E^{-1}(2^{648t})=
\mathbf1_{t\equiv6\ (7)}+
\mathbf1_{t\equiv1\ (9)}+
\mathbf1_{t\equiv14\ (15)}
\quad(t\ge2,\ 3\nmid t).
\]

This provides the following genuine fixed-blank-origin exclusion: if `t>=2`, `3∤t`, `t mod7 !=6`, `t mod9 !=1`, and `t mod15 !=14`, then the original Sheep blank-orbit starting at first-even state `10` **cannot reach `2^(648t)`**. There are exactly **132 such `t` residue classes modulo 315**, giving **132 exponent residues modulo 204,120** and natural exponent density

\[
\frac{132}{204120}=\boxed{\frac{11}{17010}}.
\]

All 132 classes are disjoint from the earlier compared 28 first-even E inverse-cone progressions and from the earlier ordinary F depth-five excluded set. This is a source-relevant all-exponent result. **It does not decide Sheep halting or BB(6).** Academic novelty beyond the explicitly compared repository sources has not been established.

## Source-defined map and proof

The authentic ordinary section law at nonterminal even `x=2^a v`, `a>=1`, odd `v>=3`, is `F(x)=x+a+3` for exceptional `v=3`, and `F(x)=x+a+(v-1)/2` for generic odd `v>=5`. Writing `F(x)-1=2^h u` for odd `u`, the next even return is `E(x)=1+3^h u`. The original six-state machine's correspondence to this first-even dynamics, including the initial even entry `10`, is established separately by [Agent16's source-importing Lean CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). Any halting power visited after initial 10 must have an incoming E edge.

**(1) Hidden-step bound.** Since `648=8*81`, the multiplicative order of 2 modulo `3^6=729` is `486`, and

`2^(648t) mod 729 = 244` when `t mod3=1`, and `487` when `t mod3=2`.

Both residues are `1+3^5*w` with `w∈{1,2}`. Consequently `v3(2^(648t)-1)=5` for all `3∤t`, and every potential incoming even edge has exactly one hidden-step count `0<=h<=5`.

**(2) All generic source valuations.** For `v>=5`, substituting the genuine F and E laws yields the exact equation

\[
2^{648t+h+1}=D(2^{a+1}+1)v+
K_h(a),\qquad
D=3^h,\quad K_h(a)=D(2a-3)+2^{h+1}.
\tag{1}
\]

For `h=0`, every `a>=2` is impossible; for `1<=h<=5`, every `a>=2h+3` is impossible. At these thresholds, `1<K_h(a)<2^a`; the bounds propagate as `a` increases because `K_h(a+1)-K_h(a)=2D` and `2^a>=2D`. But all powers of two modulo `2^(a+1)+1` have residues `±2^r` for `0<=r<=a`, none represented by an odd integer in `(1,2^a)`. This is the general signed-power residue gap used in [Agent17's uniform valuation theorem](../agent17-sheep-geometric-rays/UNIFORM-VALUATION.md) and [Agent40's earlier Lean lemma](../agent40-sheep-third-preimages/ResidueGap.lean).

Only **41** candidate pairs `(h,a)` remain: one for `h=0` and `2h+2` for each `h=1,...,5`. For each pair, let `M=3^h*(2^(a+1)+1)` and let `o` be the exact multiplicative order of 2 modulo M. The residue in equation (1) depends on `t` only modulo `q=o/gcd(o,648)`. Checking all `q` possibilities for each pair yields exactly **246 complete-period representatives** (largest q=39). All but the three rows in the table have **no** valid residue. In the surviving rows the entire residue sets are precisely `{6} mod7`, `{1} mod9`, and `{14} mod15`. The [Python exact-arithmetic certificate](certificate.py) reproduces this without a finite target cutoff or random search.

The **necessary** three-branch implication is independently proved for all natural `t,h,a,v` in [SheepPower648All.lean](SheepPower648All.lean), theorem `SheepPower648.all_generic_gates`. Its 41 constituent all-parameter modular lemmas are [SheepPower648Rows.lean](SheepPower648Rows.lean), derived from [SheepPower648Core.lean](SheepPower648Core.lean). All modules compiled **locally** under Lean 4.36.0-rc2; the unified theorem's axiom audit was exactly `[propext, Classical.choice, Quot.sound]`, with no `sorry`, `admit`, or `native_decide`. This arithmetic theorem has not yet been imported into the original-machine Lean source.

**(3) Existence of all three parents.** For a satisfying residue t, the exact period computation gives `M | 2^(648t+h+1)-K_h(a)`. The resulting quotient `v` is odd because M and K are odd and `2^(648t+h+1)` is even; `v>=5` because `t>=2` and the exponent grows. Set `x=2^a v`, whose formula is given in the table. Reversing (1) gives

\[
F(x)-1=2^h\frac{2^{648t}-1}{3^h}.
\]

The final quotient is odd for each `h<=5`, so the hidden-step count is exactly h and `E(x)=2^(648t)`. This proves **sufficiency**, and different valuations distinguish the three sources. The certificate independently evaluates the actual F/E return at representative `t=6,10,14` for the three rows; the unbounded argument is algebraic and periodic.

**(4) Exceptional sources.** For cofactor `v=3`, an incoming E edge would require

\[
2^{648t+h}+C=D(3\cdot2^a+a+3),\quad
D=3^h,\ C=D-2^h.
\]

Set `e=floor(log2(3D))`, `g=e-h`, `L=3D-2^e>0`, `U=2^(e+1)-3D>0`. The certificate checks for every `h=0,...,5` at `j=1296` that

`L*2^j>2^g*C`, `U*2^j>2^(g+1)*(D*(j+3)-C)`, and `U*2^j>=2^(g+1)*D`.

The exponential margins persist for every larger j. If `a>=j-g`, the main `3D*2^a` term is too large; if `a<j-g`, the remaining linear term cannot bridge the deficit. Thus every exceptional source is excluded, for arbitrary a and every j in the theorem.

## Relative novelty and reproducibility

In the entire excluded set, `3^5 | 2^(648t)-1`, so every target has **five genuine ordinary F ancestors**

\[
z_i=1+\frac{2^i(2^{648t}-1)}{3^i},\quad i=1,\ldots,5,
\]

all legal odd sources with `F(z_i)=z_{i-1}`, `z_0=2^(648t)`. Therefore the older ordinary F depth-five inverse-tree sieve cannot exclude any of these powers. For each of the 132 good t residues modulo315, `certificate.py` checks the exact infinite-progression disjointness criterion against all **28** published earlier E cone families (nine Agent14/16, twelve Agent22, seven later Agent14), using period `648*315=204120`. All comparisons pass. This establishes a new explicit arithmetic family relative to those sources, without claiming exhaustive external novelty or a solution for every halting exponent.

Run [certificate.py](certificate.py) with Python 3.10+ standard library. To recheck in Lean, compile `SheepPower648Core.lean` to an `.olean`, then `SheepPower648Rows.lean` to an `.olean`, then `SheepPower648All.lean`, with the directory on `LEAN_PATH` and `Std` available. Only standard logical axioms appear. The external original-machine equivalence is a separately certified dependency. [The earlier single progression result](../agent40-sheep-1296-unreachable/README.md) is strictly subsumed by this theorem.

**Outstanding research:** These excluded powers have natural density `11/17010` among *exponents*, leaving infinitely many other potential Sheep halting powers. A complete fixed-root nonhalting proof or a halting witness remains necessary. Exact BB(6) and a universal six-state upper bound remain open. This stays under `im-results/` pending broader novelty assessment and source-integrated formalization.
