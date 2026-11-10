# A doubled strict two/three-predecessor cone in the original Machine C section

**Agent 34, 10 November 2026.** Let (F=`BB6.Agent46.secNext` be the original exact first-return map of Machine C, with genuine blank-derived start ((5,1)). Let (I_r) be the set of section states admitting (r) consecutive successful predecessor transitions from arbitrary section states. Machine C and the six-state Busy Beaver problem remain unsolved.

## Theorem: strict source image and actual blank-root exclusion

For every ((x,y)\in\mathbb N^2), write (S=x+y). If
[
x\ge8,\qquad y\ge256,\qquad S\equiv4\pmod{16},\qquad 3S+2y\equiv114\pmod{128},
]
then ((x,y)\in I_2\setminus I_3) and, at **every** (t\in\mathbb N),
[
`BB6.Agent8Section.run F t (some (5,1)) \ne some (x,y)`.
]
The cone occupies exactly 16 of the 128-by-128 joint ((S\bmod128,y\bmod128)) residue cells, and therefore has natural density (1/1024) in the full lattice of section counters, outside the finite coordinate cutoffs.

This strictly extends the previous odd-right cone [OddThreeNovelty](../im-results/agent34-c-degree-profile/OddThreeNovelty.md) with (S\equiv20\pmod{32}) and (S+34\equiv2y\pmod{128}). The previous cone contained eight residue cells and had density (1/2048). The genuinely added half has (S\equiv4\pmod{32}). The full proof runs against the **unchanged original source** in [CI 42728908427](https://github.com/FlareZ123/bb6/actions/runs/42728908427).

## Exact exhaustive inverse argument

The original, source-certified all-predecessor equivalence `BB6.Agent46.section_preimage_all_iff` enumerates every direct, exceptional and recursive-bounce source case. On this cone it forces **the unique** first predecessor ((a,k)) to satisfy
[
2a+4=S,\qquad 2k+a+7=S+y,
]
and
[
a\equiv0\pmod8,\quad k\equiv0\pmod8,\quad a+k\equiv24\pmod{32}.
]
The equations construct (a=(S-4)/2), (k=(S+2y-10)/4), each at least 128. The exact predecessor iff certifies a genuine depth-zero even-bounce return ((a,k)\mapsto(x,y)). Since (k\ge128) is even, the original direct rule also constructs ((a+k-2,(k-2)/2)\mapsto(a,k)). Thus (I_2) inclusion is constructive.

For **any** second predecessor ((b,\ell)\mapsto(a,k)), the same exhaustive source iff forces
[
\ell\ge5,\qquad \ell\equiv1\pmod2,\qquad b+\ell\equiv1\pmod4.
]
The source-certified `BB6.Agent3.section_odd_image` lemma proves that any returned section state with odd second coordinate at least five must have coordinate sum (0) or (3\pmod4). Therefore ((b,\ell)) has no incoming source predecessor. This excludes *all* three-step chains regardless of bounce depth or exceptional branch.

For genuine blank time (0,1,2), the original section states are ((5,1),(3,4),(4,7)); each has second coordinate below 256. All later blank times would supply a three-step predecessor chain, already ruled out. This gives the quantified blank-root result without a time cutoff.

## New authentic high-halting parameter restriction

The unchanged Machine C necessary high stopping equation is
[
k+j+3m+5=2^{2m+2}(j+3),\qquad\text{target }(2j+3,k).
]
Theorems `BB6.Agent34OddWide.high_stop_sector` and `high_stop_bounds` establish, for **all** (j,m,k\in\mathbb N):
[
m\equiv3\pmod4,\qquad j\equiv15m+2\pmod{128}
\quad\Longrightarrow\quad
(2j+3,k)\text{ lies in the forbidden cone}.
]
In particular (m\ge3), (j\ge3), and (k\ge256). The exact source theorem `high_stop_blank_unreachable` excludes the resulting target from **every** authentic blank-origin section time.

This parameter family has exact lattice density (1/(4\cdot128)=1/512), twice the previous narrower (1/1024) odd-right family. The added (m\equiv3\pmod8) subfamily is disjoint from the old (m\equiv7\pmod8) subfamily. The concrete new example (m=3,j=47) gives (k=12739) and excluded candidate ((97,12739)). This is a necessary-gateway exclusion and is not evidence that such targets were ever blank-reachable.

As an independence diagnostic, an exact-integer implementation of the **historical named** `highAllowedValSixFull` baseline admitted each of the 32 minimal ((j\bmod128,m\bmod128)) representatives on the new lattice, including all 16 representatives of the added (m\equiv3\pmod8) subfamily. Its finite check does not constitute a kernel proof of inclusion in that prior predicate for every integer lift, or an audit against all later source-root restrictions. The new source-root nonreachability theorem is unconditional and does not use this diagnostic.

## Reproduction and proof boundary

- [OddThreeWideArithmetic.lean](../im-results/agent34-c-degree-profile/OddThreeWideArithmetic.lean) gives exact source-grammar branch elimination, including second-predecessor necessity and explicit constructive witnesses.
- [OddThreeWideSource.lean](../im-results/agent34-c-degree-profile/OddThreeWideSource.lean) transports the exhaustive arithmetic to the original `secNext`, proves (I_2\setminus I_3), arbitrary-time genuine blank exclusion, and the infinite high-halting pullback.
- [Manual original-source workflow](../.github/workflows/agent34-c-source-cone.yml) compiled the original `FastSectionDef`, `SectionAllInverse`, `Agent3CImage`, the initial-cone proofs and both new Lean modules in [successful run 42728908427](https://github.com/FlareZ123/bb6/actions/runs/42728908427). Principal proofs print ordinary logical axioms only; no `sorry` or `native_decide` appears.
- The density assertions are elementary congruence-cell counts, stated as paper corollaries rather than separately Lean-certified cardinalities.

The previously proved exact third-image density and other strict section-image hierarchies are separate global structural statements. The new family contributes an explicit original-source and authentic-root exclusion of surviving candidate forms. The **unbounded remainder** of the actual Machine C stopping quantifiers remains open, as does BB(6).
