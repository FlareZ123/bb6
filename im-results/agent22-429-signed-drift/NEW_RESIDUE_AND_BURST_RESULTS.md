# #429 blank-root branch-29: exact residue narrowing and signed-burst floors

Agent 22 — 27 November 2026. **Scope:** rigorous necessary restrictions on one #429 terminal feeder, not a machine decision. The authentic accelerated blank-start predicate is \`BB429NewResidue.Reach a b\`, starting from \`BB429.run n (0,0)\`. These results do not establish \`BB(6)\` or a lower bound on actual halting time.

## New all-time source-rooted residue theorem

The #429 odd-reset branch-29 feeder is the line
\[
(a,b)=(32q+29,\ 64q+55).
\]
Agent18's accepted \`BB429Branch29All.rooted_29_global\` already excludes every \`q<21\` and restricts \`q\bmod1024\` to 38 classes.

New full-cylinder exclusions, meaning **every nonnegative quotient, including all future blank-start times**:

* [Branch29Extra1024.lean](Branch29Extra1024.lean) excludes eight q-mod-1024 residues \`{15,47,79,191,255,383,447,639}\` (accepted **[CI 45919337704](https://github.com/FlareZ123/bb6/actions/runs/45919337704)**).
* [Branch29Extra2048.lean](Branch29Extra2048.lean) excludes 29 further q-mod-2048 residues \`{63,82,186,202,258,319,386,458,642,767,826,831,911,970,1026,1135,1151,1263,1362,1423,1519,1594,1599,1679,1738,1874,1903,1919,1978}\` (accepted **[CI 45919753140](https://github.com/FlareZ123/bb6/actions/runs/45919753140)**).
* [Branch29Roster31.lean](Branch29Roster31.lean) composes these with the unchanged Agent18 source-rooted predecessor restrictions. It proves:
\[
\operatorname{Reach}(32q+29,64q+55)\ \Longrightarrow\
q\ge21\ \land\ q\bmod2048\in S,
\]
where
\[
S=\{2,111,127,239,338,399,495,570,575,655,714,850,879,895,954,
1023,1087,1106,1210,1226,1282,1343,1410,1482,1666,1791,1850,1855,
1935,1994,2047\}.
\]
This **31/2048 necessary roster** and its exact cardinality passed **[CI 45919871438](https://github.com/FlareZ123/bb6/actions/runs/45919871438)**, with only standard Lean axioms. The remaining 31 classes are *not claimed attainable*.

The mechanism is a **shifted affine inverse-tree certificate**: a sound \`BB429Kernel.cert\` at affine index \`q=m(t+1)+r\` handles the entire tail \`q\ge m\`; an independent finite-orbit exclusion of the initial \`q=r\` covers the one remaining representative. The small-state exclusions are extended to *all time* by strict source-rank increase, never by interpreting a finite scan as a nonhalting proof. Source-level \`BB429Kernel.cert_sound\` guarantees every high-quotient exclusion. The generic arbitrary-modulus bridge is in [Branch29ShiftedCert.lean](Branch29ShiftedCert.lean), source-checked in [CI 45920525664](https://github.com/FlareZ123/bb6/actions/runs/45920525664).

## New source-connected necessary last-reset burst floors

The authentic branch-7 terminal-burst equation on the branch-29 feeder is
\[
128q+3n+131=3\cdot2^{n+2},\quad n\ge18.
\]
This forces
\[
n=127+128k,\quad c=3k+4,\quad q+c=3\cdot2^{n-5}.
\]
Agent18 had already source-proved the **necessary** floor \`n\ge16255\`. The source-connected finite-precision \`Signed429.branch29_cert_excluded\` from [SignedSource.lean](SignedSource.lean) transports a closed *signed* inverse tree of depth d to the true giant positive dyadic state when \`2d+e\le n-5\`, \`e\ge5\`, and \`2^e\ge128c-97+11d\`.

* [Branch29SignedFloor.lean](Branch29SignedFloor.lean): a kernel-reduced \`signedCert 28\` for all \`0\le k<1000\`, with \`e=20\`, proves \`n\ge128127\` for any genuinely blank-root-reachable feeder satisfying the burst equation. Accepted **[CI 45920525664](https://github.com/FlareZ123/bb6/actions/runs/45920525664)**.
* [Branch29SignedFloor10k.lean](Branch29SignedFloor10k.lean): ten separate \`signedCert 32\` batches of one thousand indices each, with \`e=26\`, prove the stronger \`n\ge1280127\` for \`k<10000\`. Accepted **[CI 45920774208](https://github.com/FlareZ123/bb6/actions/runs/45920774208)**.
* [Branch29SignedFloor1M.lean](Branch29SignedFloor1M.lean): an exact *proposed* composition of the new 31/2048 root roster with 31 corresponding k-residue classes. It checks 31 x 489 signed trees at depth48 instead of a million consecutive k. Each tree is transported with \`e=30\`. **Do not treat the proposed \`n\ge128000127\` floor as accepted before a successful complete CI run**; the Lean module and its existing workflow provide the unambiguous acceptance gate.

This analysis is particularly efficient because the last-burst equation implies
\[
q\equiv -(3k+4)\pmod{2048},
\]
so the exact source-root roster confines \`k\bmod2048\` to 31 known residues. The resulting signed certificates are substantive **finite-parameter exclusions of an unbounded blank-tape reachability question**, using previously proved all-time inverse soundness; they do not decide the unbounded \`k\) quantifier.

## Outstanding proof gap and discipline

The signed inverse trees may require unbounded, k-dependent depth. Empirical termination of the first million trees does **not** prove that every signed tree terminates; an all-parameter termination/descent theorem for the genuine branch-29 feeder would close this specific feeder without numerical cutoffs. Other #429 terminal branches and many BB(6) machines remain unresolved. The original \`SignedDrift\` / \`SignedLift\` / \`SignedSource\` source bridges remain the dependencies; neither finite simulation nor a non-positive signed state is treated as an authentic blank run.

All new modules compile under the existing pinned Lean 4.36.0-rc2 manual workflow [.github/workflows/agent22-429-signed-lift.yml](../../.github/workflows/agent22-429-signed-lift.yml) and print theorem axiom profiles. The only exceptions explicitly marked "proposed" are not to be cited as verified. There is no reliance on \`sorryAx\` or \`native_decide\` in accepted proofs.

These results currently belong in \`im-results/\` until their external academic novelty and broader contribution justify publication in \`results/\`.
