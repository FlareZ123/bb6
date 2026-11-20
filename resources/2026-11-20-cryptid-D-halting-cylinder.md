# Cryptid D: formal halting cylinder and unresolved blank-root reachability

**Retrieved:** 2026-11-20  
**Machine:** `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`  
**Normalized start:** `A(9, [])` in the @-d high-level notation.

## Exact external formal results

Two independent Lean formalizations are relevant:

1. [Google DeepMind, `cryptids`, commit `3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean) proves `HasStackReduction` for this exact machine. The file identifies it as machine #85 restarted from state D and mirrored, transports #85's closed pair-stack system, and proves a seven-raw-step blank-tape entry into that system. This is a closed-system reduction, **not** a proof that the machine halts or does not halt.
2. [@-d, `int-y1/proofs`, commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0`](https://github.com/int-y1/proofs/blob/1929f57df4dd7afcc11c3f458e20526fd1f991e0/BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean) directly defines the exact six-state transition table in a separate `TM62` semantics. It proves:
   - `reach_9_nil : c₀ ⊢* A 9 []` (36 raw steps);
   - `halts_A_mod_3_pow_108 (k : Nat)`: every `A(3^108*k + C, [])` halts, where
     `C = 1975700577069254261393123959451562008800234946348086`.

Thus the *halting cylinder itself* is formally proved in an independent Lean development. The blank-root question is whether the actual orbit from `A(9, [])` ever enters this cylinder (or another halting cylinder). The proof does **not** establish that reachability.

## Explicit 108-step branch word

The BusyBeaverWiki analysis by @-d gives the following E/B branch word of length 108:

`EEBBEBEEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEEEBBEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEBEEBBEBBEEEBBEBBEBE`

It contains 53 E and 55 B symbols. Its corresponding residue class is the `A(3^108*k+C, [])` cylinder above. The word is a concrete halting route, not a proof that the blank-root orbit follows it.

Primary community analysis: [BusyBeaverWiki #85 / #490 page](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA). The page records that:
- #490 is the D-start normalized machine and starts at `A(9, "")`;
- @-d's BFS over roughly 235,000 suffix words found the length-108 E/B path;
- the open question is whether the orbit from `A(9, "")` reaches `A(3^108*k+C, ""));
- a simulation through 2,728,570 A-states did not complete the path; its closest reported attempt matched 21 of 108 letters.

These simulation counts and the estimated expected halting time (roughly (10^{10^{38.1}}) raw steps) are **empirical/heuristic**, not formal bounds or a halting proof. The page also reports many possible length-108 paths, but the cited Lean theorem above certifies the one residue cylinder it states; do not silently promote the broader path count to a formal theorem.

## Consequence for this repository

The D objective should be framed as a **halting-reachability problem**, not as a presumed all-time nonhalting problem. The existing source-certified DRegular sections and exceptional reentries remain useful finite-prefix machinery, but their value is measured by whether they can be connected to the high-level `A(n,r)` orbit and ultimately to a halting cylinder.

The current repository's arithmetic seed `seed9 = (9,0,0)` is intended to represent the normalized `A(9, [])` start, but the exact bridge between `DRegularSource.sourceSection` and the external `A(n,r)` semantics must be proved before treating the two representations as definitionally or theorem-level identical.

Highest-value next work:
1. prove a source-exact correspondence between the repository's DRegular section and @-d's `A(n,r)` macro, including the E/B/A branch labels and suffix update;
2. derive the exact preimage/cylinder conditions for the 108-step word in the repository's own model;
3. investigate whether the orbit from `A(9, [])` reaches that cylinder, another certified halting cylinder, or is provably excluded from all of them;
4. use exact modular/3-adic structure to replace the uninformative 2.7-million-step finite screen. Do not treat a probabilistic heuristic or a long finite prefix as a proof of eventual reachability.

This result concerns one BB(6) holdout and does not determine the global Busy Beaver value.
